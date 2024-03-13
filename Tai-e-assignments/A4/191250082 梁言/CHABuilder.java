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
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

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
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while(!workList.isEmpty()){
            JMethod method = workList.remove();
            if(!callGraph.reachableMethods.contains(method)){
                callGraph.addReachableMethod(method);
                if(!method.isAbstract()){
                    for(Stmt stmt :method.getIR().getStmts()){
                        if(stmt instanceof Invoke invoke){
                            Set<JMethod> methods = resolve(invoke);
                            for(JMethod m : methods){
                                workList.add(m);
                                callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m));

                            }
                        }
                    };
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
        Set<JMethod> res =  new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        JMethod m = methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature());
        //m == null的判断不能在最外面，因为invokevirtual中该类的该方法很有可能是null,所以要在里面判断if(m == null)
        if(callSite.isStatic()){
            if(m != null)
                res.add(m);
            return res;
        }
        else if(callSite.isSpecial()){
            JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
            JMethod method = dispatch(declaringClass, methodRef.getSubsignature());
            if(method != null)
                res.add(method);
            return res;
        }
        else if(callSite.isVirtual() || callSite.isInterface()){
            JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
            Queue<JClass> classList = new LinkedList<>();
            classList.add(declaringClass);
            //先加入直接子类，然后再递归加子类的子类，这样可以避免重复
            while(!classList.isEmpty()){
                JClass top = classList.remove();
                if(top.isInterface()){
                    classList.addAll(hierarchy.getDirectSubinterfacesOf(top));
                    classList.addAll(hierarchy.getDirectImplementorsOf(top));
                }else{
                    classList.addAll(hierarchy.getDirectSubclassesOf(top));
                }
                //然后把dispatch的结果加进去
                JMethod method = dispatch(top, methodRef.getSubsignature());
                if(method!= null && !method.isAbstract())
                    res.add(method);
            }
        }
        return res;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        //首先查找自己有没有
        if(jclass.getDeclaredMethod(subsignature) != null)
            return jclass.getDeclaredMethod(subsignature);
        if(jclass.getSuperClass() != null)
            return dispatch(jclass.getSuperClass(), subsignature);
        //都没有找到就返回null
        return null;
    }
}
