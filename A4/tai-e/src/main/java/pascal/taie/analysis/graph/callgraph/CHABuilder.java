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
            JMethod method = worklist.poll();

            if (!callGraph.addReachableMethod(method)) {
                continue;
            }

            for (Invoke callSite : callGraph.getCallSitesIn(method)) {
                Set<JMethod> callees = resolve(callSite);

                for (JMethod callee : callees) {
                    CallKind kind;

                    if (callSite.isInterface()) {
                        kind = CallKind.INTERFACE;
                    } else if (callSite.isVirtual()) {
                        kind = CallKind.VIRTUAL;
                    } else if (callSite.isSpecial()) {
                        kind = CallKind.SPECIAL;
                    } else if (callSite.isStatic()) {
                        kind = CallKind.STATIC;
                    } else if (callSite.isDynamic()) {
                        kind = CallKind.DYNAMIC;
                    } else {
                        kind = CallKind.OTHER;
                    }

                    Edge<Invoke, JMethod> edge =
                            new Edge<>(kind, callSite, callee);

                    callGraph.addEdge(edge);
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
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaredClass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();

        // Static and special calls have a single statically determined target.
        if (callSite.isStatic() || callSite.isSpecial()) {
            Set<JClass> allClasses = hierarchy.allClasses()
                    .collect(java.util.stream.Collectors.toSet());
            Set<JClass> visited = new HashSet<>();
            Queue<JClass> worklist = new ArrayDeque<>();
            worklist.add(declaredClass);

            while (!worklist.isEmpty()) {
                JClass jclass = worklist.poll();
                if (!visited.add(jclass)) {
                    continue;
                }

                JMethod target = dispatch(jclass, subsignature);
                if (target != null) {
                    return Set.of(target);
                }

                for (JClass candidate : allClasses) {
                    if (hierarchy.getDirectSubclassesOf(candidate)
                            .contains(jclass)
                            || hierarchy.getDirectSubinterfacesOf(candidate)
                            .contains(jclass)
                            || hierarchy.getDirectImplementorsOf(candidate)
                            .contains(jclass)) {
                        worklist.add(candidate);
                    }
                }
            }

            return Set.of();
        }

        Set<JMethod> targets = new HashSet<>();
        Set<JClass> allClasses = hierarchy.allClasses()
                .collect(java.util.stream.Collectors.toSet());

        // Find the nearest concrete implementation inherited by the
        // declared receiver type, without expanding that ancestor's siblings.
        Set<JClass> visitedAncestors = new HashSet<>();
        Queue<JClass> ancestors = new ArrayDeque<>();
        ancestors.add(declaredClass);
        while (!ancestors.isEmpty()) {
            JClass jclass = ancestors.poll();
            if (!visitedAncestors.add(jclass)) {
                continue;
            }

            JMethod target = dispatch(jclass, subsignature);
            if (target != null) {
                targets.add(target);
                continue;
            }

            for (JClass candidate : allClasses) {
                if (hierarchy.getDirectSubclassesOf(candidate)
                        .contains(jclass)
                        || hierarchy.getDirectSubinterfacesOf(candidate)
                        .contains(jclass)
                        || hierarchy.getDirectImplementorsOf(candidate)
                        .contains(jclass)) {
                    ancestors.add(candidate);
                }
            }
        }

        // Find implementations in the declared receiver type's descendants.
        Set<JClass> visitedDescendants = new HashSet<>();
        Queue<JClass> descendants = new ArrayDeque<>();
        descendants.add(declaredClass);
        while (!descendants.isEmpty()) {
            JClass jclass = descendants.poll();
            if (!visitedDescendants.add(jclass)) {
                continue;
            }

            JMethod target = dispatch(jclass, subsignature);
            if (target != null) {
                targets.add(target);
            } else {
                // The candidate may inherit the implementation from a
                // superclass or superinterface without overriding it.
                Set<JClass> inheritedVisited = new HashSet<>();
                Queue<JClass> inherited = new ArrayDeque<>();
                inherited.add(jclass);

                while (!inherited.isEmpty()) {
                    JClass parentCandidate = inherited.poll();
                    if (!inheritedVisited.add(parentCandidate)) {
                        continue;
                    }

                    JMethod inheritedTarget = dispatch(
                            parentCandidate, subsignature);
                    if (inheritedTarget != null) {
                        targets.add(inheritedTarget);
                        break;
                    }

                    for (JClass candidate : allClasses) {
                        if (hierarchy.getDirectSubclassesOf(candidate)
                                .contains(parentCandidate)
                                || hierarchy.getDirectSubinterfacesOf(candidate)
                                .contains(parentCandidate)
                                || hierarchy.getDirectImplementorsOf(candidate)
                                .contains(parentCandidate)) {
                            inherited.add(candidate);
                        }
                    }
                }
            }

            if (jclass.isInterface()) {
                descendants.addAll(
                        hierarchy.getDirectSubinterfacesOf(jclass));
                descendants.addAll(
                        hierarchy.getDirectImplementorsOf(jclass));
            } else {
                descendants.addAll(
                        hierarchy.getDirectSubclassesOf(jclass));
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
        JMethod method = jclass.getDeclaredMethod(subsignature);

        if (method != null && !method.isAbstract()) {
            return method;
        }

        return null;
    }
}
