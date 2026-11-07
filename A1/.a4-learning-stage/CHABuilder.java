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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me

        Queue<JMethod> worklist = new ArrayDeque<>();
        worklist.add(entry);

        while (!worklist.isEmpty()) {
            JMethod method = worklist.remove();

            // 首次登记时，也会收集该方法中的调用点
            if (!callGraph.addReachableMethod(method)) {
                continue;
            }

            for (Invoke callSite : callGraph.getCallSitesIn(method)) {
                for (JMethod callee : resolve(callSite)) {
                    callGraph.addEdge(new Edge<>(
                            CallGraphs.getCallKind(callSite),
                            callSite,
                            callee
                    ));

                    worklist.add(callee);
                }
            }
        }


        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> targets = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();

        // 静态调用、特殊调用
        if (callSite.isStatic() || callSite.isSpecial()) {
            JMethod target = dispatch(methodRef.getDeclaringClass(),
                    methodRef.getSubsignature());
            if (target != null) {
                targets.add(target);
            }
            return targets;
        }

        // 本实验另外处理虚调用和接口调用
        if (callSite.isVirtual() || callSite.isInterface()) {
            Queue<JClass> worklist = new ArrayDeque<>();
            Set<JClass> visited = new HashSet<>();

            worklist.add(methodRef.getDeclaringClass());

            while (!worklist.isEmpty()) {
                JClass current = worklist.remove();

                if (!visited.add(current)) {
                    continue;
                }

                if (current.isInterface()) {
                    // 沿接口继承关系、接口实现关系向下遍历
                    worklist.addAll(
                            hierarchy.getDirectSubinterfacesOf(current));
                    worklist.addAll(
                            hierarchy.getDirectImplementorsOf(current));
                } else {
                    // 具体类才可能作为对象的实际类型
                    if (!current.isAbstract()) {
                        JMethod target = dispatch(
                                current, methodRef.getSubsignature());

                        if (target != null) {
                            targets.add(target);
                        }
                    }

                    // 抽象类也必须继续遍历其子类
                    worklist.addAll(
                            hierarchy.getDirectSubclassesOf(current));
                }
            }
        }

        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        while (jclass != null) {
            JMethod method = jclass.getDeclaredMethod(subsignature);

            if (method != null) {
                return method.isAbstract() ? null : method;
            }

            jclass = jclass.getSuperClass();
        }

        return null;
    }
}

