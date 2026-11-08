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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method) && !method.isAbstract()) {
            method.getIR().forEach(stmt -> stmt.accept(stmtProcessor));
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            VarPtr target = pointerFlowGraph.getVarPtr(stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            workList.addEntry(target, new PointsToSet(obj));
            return null;
        }


        @Override
        public Void visit(Copy stmt) {
            VarPtr source = pointerFlowGraph.getVarPtr(stmt.getRValue());
            VarPtr target = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                if (callee != null) {
                    addCallEdge(stmt, callee);
                }
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                Pointer field = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), field);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                Pointer field = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(field, pointerFlowGraph.getVarPtr(stmt.getLValue()));
            }
            return null;
        }

        private void addCallEdge(Invoke callSite, JMethod callee) {
            Edge<Invoke, JMethod> edge =
                    new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee);
            if (!callGraph.addEdge(edge)) {
                return;
            }

            addReachable(callee);
            IR calleeIR = callee.getIR();
            InvokeExp invoke = callSite.getInvokeExp();

            for (int i = 0; i < invoke.getArgCount(); i++) {
                Var param = calleeIR.getParam(i);
                addPFGEdge(pointerFlowGraph.getVarPtr(invoke.getArg(i)),
                        pointerFlowGraph.getVarPtr(param));
            }

            Var result = callSite.getResult();
            if (result != null) {
                for (Var returnVar : calleeIR.getReturnVars()) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(returnVar),
                            pointerFlowGraph.getVarPtr(result));
                }
            }
        }


    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target) && !source.getPointsToSet().isEmpty()) {
            workList.addEntry(target, source.getPointsToSet());
        }

    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me

        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet delta = propagate(pointer, entry.pointsToSet());

            if (pointer instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : delta) {
                    for (StoreField store : var.getStoreFields()) {
                        Pointer field = pointerFlowGraph.getInstanceField(
                                obj, store.getFieldRef().resolve());
                        addPFGEdge(pointerFlowGraph.getVarPtr(store.getRValue()), field);
                    }

                    for (LoadField load : var.getLoadFields()) {
                        Pointer field = pointerFlowGraph.getInstanceField(
                                obj, load.getFieldRef().resolve());
                        addPFGEdge(field, pointerFlowGraph.getVarPtr(load.getLValue()));
                    }

                    for (StoreArray store : var.getStoreArrays()) {
                        Var value = store.getRValue();
                        addPFGEdge(pointerFlowGraph.getVarPtr(value),
                                pointerFlowGraph.getArrayIndex(obj));
                    }

                    for (LoadArray load : var.getLoadArrays()) {
                        Var result = load.getLValue();
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(result));
                    }

                    processCall(var, obj);
                }
            }

        }



    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet current = pointer.getPointsToSet();
        PointsToSet delta = new PointsToSet();

        for (Obj obj : pointsToSet) {
            if (current.addObject(obj)) {
                delta.addObject(obj);
            }
        }

        if (!delta.isEmpty()) {
            for (Pointer successor : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(successor, delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me

        for (Invoke callSite : var.getInvokes()) {
            JMethod callee = resolveCallee(recv, callSite);
            if (callee == null) {
                continue;
            }

            stmtProcessor.addCallEdge(callSite, callee);

            Var thisVar = callee.getIR().getThis();
            VarPtr thisPtr = pointerFlowGraph.getVarPtr(thisVar);
            workList.addEntry(thisPtr, new PointsToSet(recv));
        }

    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
