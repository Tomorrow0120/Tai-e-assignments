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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;

import java.util.Collections;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    private PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    private boolean mayAlias(Var first, Var second) {
        return !Collections.disjoint(
                pta.getPointsToSet(first),
                pta.getPointsToSet(second));
    }

    private boolean mayAliasIndex(Value first, Value second) {
        if (first.isUndef() || second.isUndef()) {
            return false;
        }

        if (first.isNAC() || second.isNAC()) {
            return true;
        }

        return first.getConstant() == second.getConstant();
    }

    private Value readArrayValue(LoadArray load, CPFact loadIn) {
        ArrayAccess loadAccess = load.getArrayAccess();
        Value loadIndex = loadIn.get(loadAccess.getIndex());
        Value value = Value.getUndef();

        for (Stmt candidate : icfg) {
            if (!(candidate instanceof StoreArray store)) {
                continue;
            }

            ArrayAccess storeAccess = store.getArrayAccess();

            if (!mayAlias(loadAccess.getBase(), storeAccess.getBase())) {
                continue;
            }

            CPFact storeIn = solver.getInFact(store);
            Value storeIndex = storeIn.get(storeAccess.getIndex());

            if (!mayAliasIndex(loadIndex, storeIndex)) {
                continue;
            }

            Value storedValue = storeIn.get(store.getRValue());
            value = cp.meetValue(value, storedValue);
        }

        return value;
    }

    private Value readFieldValue(LoadField load) {
        Value value = Value.getUndef();

        for (Stmt candidate : icfg) {
            if (!(candidate instanceof StoreField store)) {
                continue;
            }

            if (!load.getFieldRef().resolve()
                    .equals(store.getFieldRef().resolve())) {
                continue;
            }

            if (!load.isStatic()) {
                Var loadBase =
                        ((InstanceFieldAccess) load.getFieldAccess()).getBase();
                Var storeBase =
                        ((InstanceFieldAccess) store.getFieldAccess()).getBase();

                if (!mayAlias(loadBase, storeBase)) {
                    continue;
                }
            }

            CPFact storeIn = solver.getInFact(store);
            Value storedValue = storeIn.get(store.getRValue());
            value = cp.meetValue(value, storedValue);
        }

        return value;
    }

    private void notifyArrayLoads(StoreArray store) {
        Var storeBase = store.getArrayAccess().getBase();

        for (Stmt candidate : icfg) {
            if (!(candidate instanceof LoadArray load)
                    || !ConstantPropagation.canHoldInt(load.getLValue())) {
                continue;
            }

            Var loadBase = load.getArrayAccess().getBase();

            if (mayAlias(storeBase, loadBase)) {
                solver.addToWorkList(load);
            }
        }
    }

    private void notifyFieldLoads(StoreField store) {
        for (Stmt candidate : icfg) {
            if (!(candidate instanceof LoadField load)
                    || !ConstantPropagation.canHoldInt(load.getLValue())) {
                continue;
            }

            if (!store.getFieldRef().resolve()
                    .equals(load.getFieldRef().resolve())) {
                continue;
            }

            if (!store.isStatic()) {
                Var storeBase =
                        ((InstanceFieldAccess) store.getFieldAccess()).getBase();
                Var loadBase =
                        ((InstanceFieldAccess) load.getFieldAccess()).getBase();

                if (!mayAlias(storeBase, loadBase)) {
                    continue;
                }
            }

            solver.addToWorkList(load);
        }
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact oldOut = out.copy();

        out.clear();
        out.copyFrom(in);

        return !out.equals(oldOut);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof LoadField load
                && ConstantPropagation.canHoldInt(load.getLValue())) {
            CPFact oldOut = out.copy();

            out.clear();
            out.copyFrom(in);
            out.update(load.getLValue(), readFieldValue(load));

            return !out.equals(oldOut);
        }

        if (stmt instanceof StoreField store
                && ConstantPropagation.canHoldInt(store.getRValue())) {
            notifyFieldLoads(store);
        }
        if (stmt instanceof LoadArray load
                && ConstantPropagation.canHoldInt(load.getLValue())) {
            CPFact oldOut = out.copy();

            out.clear();
            out.copyFrom(in);
            out.update(load.getLValue(), readArrayValue(load, in));

            return !out.equals(oldOut);
        }
        if (stmt instanceof StoreArray store
                && ConstantPropagation.canHoldInt(store.getRValue())) {
            notifyArrayLoads(store);
        }

        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact fact = out.copy();
        Invoke call = (Invoke) edge.getSource();

        Var result = call.getResult();
        if (result != null) {
            fact.remove(result);
        }

        return fact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Invoke call = (Invoke) edge.getSource();
        InvokeExp invokeExp = call.getInvokeExp();
        IR calleeIR = edge.getCallee().getIR();

        CPFact entryFact = new CPFact();

        for (int i = 0; i < invokeExp.getArgCount(); i++) {
            Var param = calleeIR.getParam(i);

            if (ConstantPropagation.canHoldInt(param)) {
                Var arg = invokeExp.getArg(i);
                entryFact.update(param, callSiteOut.get(arg));
            }
        }

        return entryFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact fact = new CPFact();
        Invoke call = (Invoke) edge.getCallSite();
        Var result = call.getResult();

        if (result != null && ConstantPropagation.canHoldInt(result)) {
            Value value = Value.getUndef();

            for (Var returnVar : edge.getReturnVars()) {
                value = cp.meetValue(value, returnOut.get(returnVar));
            }

            fact.update(result, value);
        }

        return fact;
    }
}
