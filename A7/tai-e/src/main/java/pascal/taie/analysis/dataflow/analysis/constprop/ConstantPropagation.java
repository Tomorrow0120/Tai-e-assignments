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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact boundary = new CPFact();
        // 方法参数初始化为 NAC（值未知）
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                boundary.update(param, Value.getNAC());
            }
        }
        return boundary;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var : fact.keySet()) {
            Value v1 = target.get(var);
            Value v2 = fact.get(var);
            Value result = meetValue(v1, v2);
            target.update(var, result);
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isUndef()){
            return v2;
        }
        if(v2.isUndef())
            return v1;
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.getConstant() == v2.getConstant()) {
            return v1;
        }
        else {
            return Value.getNAC();
        }

    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact oldOut = out.copy();
        out.copyFrom(in);

        if (stmt instanceof DefinitionStmt<?, ?> defStmt) {
            var lhs = defStmt.getLValue();
            var rhs = defStmt.getRValue();
            if (lhs instanceof Var x && canHoldInt(x)) {
                Value v = evaluate(rhs, in);
                out.update(x, v);
            }
        }

        return !out.equals(oldOut);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral literal) {
            return Value.makeConstant(literal.getValue());
        }

        // 情况 2：变量，从 fact 里取它的值
        if (exp instanceof Var var) {
            return in.get(var);
        }

        // 情况 3：二元运算，比如 a + b
        if (exp instanceof BinaryExp binary) {
            Value v1 = evaluate(binary.getOperand1(), in);
            Value v2 = evaluate(binary.getOperand2(), in);

            // 有一个是 NAC，结果就是 NAC；
            // 特殊处理：NAC / 0 和 NAC % 0 在运行时必然抛异常，
            // 变量不会被赋值，因此结果应为 UNDEF 而非 NAC
            if (v1.isNAC() || v2.isNAC()) {
                if (v1.isNAC() && v2.isConstant()
                        && binary instanceof ArithmeticExp arith0
                        && (arith0.getOperator() == ArithmeticExp.Op.DIV
                        || arith0.getOperator() == ArithmeticExp.Op.REM)
                        && v2.getConstant() == 0) {
                    return Value.getUndef();
                }
                return Value.getNAC();
            }

            // 有一个是 UNDEF，结果就是 UNDEF
            if (v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            }

            // 两个都是常量，做运算
            int a = v1.getConstant();
            int b = v2.getConstant();

            if (binary instanceof ArithmeticExp arith) {
                // 除数为 0 时除法/取余会抛异常，变量不会被赋值，结果为 UNDEF
                if ((arith.getOperator() == ArithmeticExp.Op.DIV
                        || arith.getOperator() == ArithmeticExp.Op.REM)
                        && b == 0) {
                    return Value.getUndef();
                }
                return switch (arith.getOperator()) {
                    case ADD -> Value.makeConstant(a + b);
                    case SUB -> Value.makeConstant(a - b);
                    case MUL -> Value.makeConstant(a * b);
                    case DIV -> Value.makeConstant(a / b);
                    case REM -> Value.makeConstant(a % b);
                };
            }

            // 条件表达式（==, !=, <, >, <=, >=）：常量为真返回 1，为假返回 0
            if (binary instanceof ConditionExp cond) {
                boolean result = switch (cond.getOperator()) {
                    case EQ -> a == b;
                    case NE -> a != b;
                    case LT -> a < b;
                    case GT -> a > b;
                    case LE -> a <= b;
                    case GE -> a >= b;
                };
                return Value.makeConstant(result ? 1 : 0);
            }

            if (binary instanceof ShiftExp shift) {
                return switch (shift.getOperator()) {
                    case SHL -> Value.makeConstant(a << b);
                    case SHR -> Value.makeConstant(a >> b);
                    case USHR -> Value.makeConstant(a >>> b);
                };
            }

            if (binary instanceof BitwiseExp bitwise) {
                return switch (bitwise.getOperator()) {
                    case OR -> Value.makeConstant(a | b);
                    case AND -> Value.makeConstant(a & b);
                    case XOR -> Value.makeConstant(a ^ b);
                };
            }

            // 其他二元运算类型，统一返回 NAC
            return Value.getNAC();
        }


        // 其他表达式（方法调用、字段访问等）都是 NAC
        return Value.getNAC();
    }
}
