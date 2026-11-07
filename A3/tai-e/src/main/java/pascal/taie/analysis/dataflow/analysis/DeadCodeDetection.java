/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants = ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars = ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // ---- 1. 可达性分析：结合常量传播裁剪 if / switch 分支 ----
        Set<Stmt> reachable = new HashSet<>();
        Deque<Stmt> worklist = new ArrayDeque<>();
        worklist.add(cfg.getEntry());

        while (!worklist.isEmpty()) {
            Stmt stmt = worklist.removeFirst();
            // 已访问则跳过
            if (!reachable.add(stmt)) {
                continue;
            }

            // 求出该分支语句的常量值（若有）
            Value value = null;
            if (stmt instanceof If) {
                If ifStmt = (If) stmt;
                value = ConstantPropagation.evaluate(
                        ifStmt.getCondition(), constants.getInFact(stmt));
            } else if (stmt instanceof SwitchStmt) {
                SwitchStmt switchStmt = (SwitchStmt) stmt;
                value = constants.getInFact(stmt).get(switchStmt.getVar());
            }

            // 遍历出边，决定走哪些
            for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                boolean follow = true;

                if (stmt instanceof If && value != null && value.isConstant()) {
                    // 条件为真走 IF_TRUE，为假走 IF_FALSE
                    if (value.getConstant() != 0) {
                        follow = edge.getKind() == Edge.Kind.IF_TRUE;
                    } else {
                        follow = edge.getKind() == Edge.Kind.IF_FALSE;
                    }
                }

                if (stmt instanceof SwitchStmt && value != null && value.isConstant()) {
                    SwitchStmt switchStmt = (SwitchStmt) stmt;
                    int constant = value.getConstant();
                    if (switchStmt.getCaseValues().contains(constant)) {
                        // 命中某个 case：只走对应的 SWITCH_CASE 边
                        follow = edge.isSwitchCase() && edge.getCaseValue() == constant;
                    } else {
                        // 未命中任何 case：只走 SWITCH_DEFAULT 边
                        follow = edge.getKind() == Edge.Kind.SWITCH_DEFAULT;
                    }
                }

                if (follow) {
                    worklist.addLast(edge.getTarget());
                }
            }
        }

        // ---- 2. 不可达语句即为死代码（排除 entry / exit）----
        for (Stmt stmt : cfg) {
            if (!reachable.contains(stmt) && !cfg.isEntry(stmt) && !cfg.isExit(stmt)) {
                deadCode.add(stmt);
            }
        }

        // ---- 3. 死赋值检测：仅针对可达语句 ----
        for (Stmt stmt : reachable) {
            if (stmt instanceof AssignStmt<?, ?>) {
                AssignStmt<?, ?> assign = (AssignStmt<?, ?>) stmt;
                // 左值必须是变量
                if (assign.getLValue() instanceof Var) {
                    Var var = (Var) assign.getLValue();
                    // 该变量在 out 中不活跃，且右值无副作用 => 死赋值
                    // （x = a / b 这类可能抛异常的会被 hasNoSideEffect 拦下，予以保留）
                    if (!liveVars.getOutFact(stmt).contains(var)
                            && hasNoSideEffect(assign.getRValue())) {
                        deadCode.add(stmt);
                    }
                }
            }
        }



        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
