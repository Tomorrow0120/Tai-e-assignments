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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final Map<CSVar, Set<TransferTarget>> transfersByFrom =
            new HashMap<>();

    private record TransferTarget(CSVar target, Type type) {}

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    private Var getTransferVar(Invoke invoke, int position) {
        return switch (position) {
            case TaintTransfer.BASE ->
                    invoke.getInvokeExp() instanceof InvokeInstanceExp instance
                            ? instance.getBase() : null;
            case TaintTransfer.RESULT -> invoke.getResult();
            default -> invoke.getInvokeExp().getArg(position);
        };
    }

    private void transferTaint(CSObj fromObj, CSVar target, Type targetType) {
        var obj = fromObj.getObject();
        if (!manager.isTaint(obj)) {
            return;
        }

        Invoke sourceCall = manager.getSourceCall(obj);
        var taint = manager.makeTaint(sourceCall, targetType);
        CSObj csTaint = csManager.getCSObj(emptyContext, taint);
        solver.addPointsTo(target, csTaint);
    }

    public void processSource(CSCallSite callSite, JMethod callee) {
        Invoke invoke = callSite.getCallSite();
        Var result = invoke.getResult();
        if (result == null) {
            return;
        }

        for (Source source : config.getSources()) {
            if (!source.method().equals(callee)) {
                continue;
            }

            CSVar target = csManager.getCSVar(callSite.getContext(), result);
            CSObj taint = csManager.getCSObj(
                    emptyContext, manager.makeTaint(invoke, source.type()));

            solver.addPointsTo(target, taint);
        }
    }

    public void registerTransfers(CSCallSite callSite, JMethod callee) {
        Invoke invoke = callSite.getCallSite();
        Context context = callSite.getContext();

        for (TaintTransfer rule : config.getTransfers()) {
            if (!rule.method().equals(callee)) {
                continue;
            }

            Var fromVar = getTransferVar(invoke, rule.from());
            Var toVar = getTransferVar(invoke, rule.to());
            if (fromVar == null || toVar == null) {
                continue;
            }

            CSVar from = csManager.getCSVar(context, fromVar);
            CSVar to = csManager.getCSVar(context, toVar);

            // 记下来，留给以后到达的污点。
            transfersByFrom.computeIfAbsent(from, key -> new HashSet<>())
                    .add(new TransferTarget(to, rule.type()));

            // 检查已经到达的对象，有污点就传过去。
            var objects = from.getPointsToSet();
            if (objects != null) {
                for (CSObj obj : objects) {
                    transferTaint(obj, to, rule.type());
                }
            }
        }
    }

    public void onNewPointsTo(CSVar from, PointsToSet delta) {
        var targets = transfersByFrom.get(from);
        if (targets == null) {
            return;
        }

        for (CSObj obj : delta) {
            for (TransferTarget target : targets) {
                transferTaint(obj, target.target(), target.type());
            }
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }



    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        result.getCSCallGraph().edges().forEach(edge -> {
            var callSite = edge.getCallSite();
            Invoke invoke = callSite.getCallSite();

            for (Sink sink : config.getSinks()) {
                if (!sink.method().equals(edge.getCallee().getMethod())) {
                    continue;
                }

                int index = sink.index();
                var arg = invoke.getInvokeExp().getArg(index);
                var csArg = csManager.getCSVar(callSite.getContext(), arg);

                for (var csObj : result.getPointsToSet(csArg)) {
                    var obj = csObj.getObject();
                    if (manager.isTaint(obj)) {
                        taintFlows.add(new TaintFlow(
                                manager.getSourceCall(obj), invoke, index));
                    }
                }
            }
        });

        return taintFlows;
    }
}
