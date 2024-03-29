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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if(!callGraph.contains(csMethod)){
            callGraph.addReachableMethod(csMethod);
            Context context = csMethod.getContext();
            List<Stmt> statements = csMethod.getMethod().getIR().getStmts();
            for(Stmt statement: statements){
                //处理所有x = new T()语句
                if (statement instanceof New allocSite){
                    Var var = allocSite.getLValue();
                    Obj obj = heapModel.getObj(allocSite);
                    //选择新创建对象obj的heapContext
                    Context objContext = contextSelector.selectHeapContext(csMethod,obj);
                    CSVar varPtr = csManager.getCSVar(context,var);
                    CSObj csObj = csManager.getCSObj(objContext,obj);
//                    varPtr.getPointsToSet().addObject(obj);
                    workList.addEntry(varPtr, PointsToSetFactory.make(csObj));
                }
                //处理所有非静态x = y的copy语句
                if (statement instanceof Copy copySite){
                    Var target = copySite.getLValue();
                    Var source = copySite.getRValue();
                    CSVar sourcePtr = csManager.getCSVar(context,source);
                    CSVar targetPtr = csManager.getCSVar(context,target);
                    addPFGEdge(sourcePtr,targetPtr);
                }
                //处理静态的load方法 y = T.f
                if(statement instanceof LoadField loadField && loadField.isStatic()){
                    CSVar target = csManager.getCSVar(context,loadField.getLValue());
                    StaticField staticField = csManager.getStaticField(loadField.getFieldRef().resolve());
                    addPFGEdge(staticField, target);
                }
                //处理静态的store方法 T.f = y
                if(statement instanceof StoreField storeField && storeField.isStatic()){
                    CSVar source = csManager.getCSVar(context,storeField.getRValue());
                    StaticField staticField = csManager.getStaticField(storeField.getFieldRef().resolve());
                    addPFGEdge(source,staticField);
                }
                //处理静态的方法调用
                if(statement instanceof Invoke invoke && invoke.isStatic()){
                    JMethod jmethod = resolveCallee(null,invoke);
                    CSCallSite csCallSite = csManager.getCSCallSite(context,invoke);
                    Context calleeContext = contextSelector.selectContext(csCallSite,jmethod);
                    CSMethod calleeMethod = csManager.getCSMethod(calleeContext,jmethod);
                    if(!callGraph.getCallersOf(calleeMethod).contains(csCallSite)){
                        callGraph.addEdge(new Edge<>(CallKind.SPECIAL, csCallSite,calleeMethod));
                        addReachable(calleeMethod);
                        List<Var> actualParams = invoke.getInvokeExp().getArgs();
                        List<Var> funcParams = jmethod.getIR().getParams();
                        List<Var> returnVar = jmethod.getIR().getReturnVars();
                        for(int i = 0; i < actualParams.size(); i ++){
                            addPFGEdge(csManager.getCSVar(context, actualParams.get(i)), csManager.getCSVar(calleeContext, funcParams.get(i)));
                        }
                        //如果有返回值
                        Var mret = invoke.getLValue();
                        if(mret != null){
                            for (Var value : returnVar) {
                                addPFGEdge(csManager.getCSVar(calleeContext, value), csManager.getCSVar(context, mret));
                            }
                        }

                    }
                }
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        //说明没有s->t的这条边
        if(!pointerFlowGraph.getSuccsOf(source).contains(target)){
            pointerFlowGraph.addEdge(source,target);
            PointsToSet pointsToSet = source.getPointsToSet();
            if(!pointsToSet.isEmpty()){
                workList.addEntry(target,pointsToSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet pts = entry.pointsToSet();
            Pointer n = entry.pointer();
            PointsToSet delta = propagate(n,pts);
            if(n instanceof CSVar csVar){
                Var var = csVar.getVar();
                Context context = csVar.getContext();
                Set<CSObj> objects = delta.getObjects();
                for(CSObj obj: objects){
                    List<StoreField> storeFields = var.getStoreFields();
                    for(StoreField storeField: storeFields){
                        addPFGEdge(csManager.getCSVar(context, storeField.getRValue()), csManager.getInstanceField(obj,storeField.getFieldRef().resolve()));
                    }
                    List<LoadField> loadFields = var.getLoadFields();
                    for(LoadField loadField: loadFields){
                        addPFGEdge(csManager.getInstanceField(obj,loadField.getFieldRef().resolve()),csManager.getCSVar(context, loadField.getLValue()));
                    }
                    List<StoreArray> storeArrays = var.getStoreArrays();
                    for(StoreArray storeArray: storeArrays){
                        addPFGEdge(csManager.getCSVar(context, storeArray.getRValue()), csManager.getArrayIndex(obj));
                    }
                    List<LoadArray> loadArrays = var.getLoadArrays();
                    for(LoadArray loadArray: loadArrays){
                        addPFGEdge(csManager.getArrayIndex(obj), csManager.getCSVar(context, loadArray.getLValue()));
                    }
                    processCall(csVar, obj);
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
        //delta = pts - ptn
        PointsToSet ptn = pointer.getPointsToSet();
        PointsToSet delta = PointsToSetFactory.make();
        Set<CSObj> pts = pointsToSet.getObjects();
        // ptn U= pts
        for(CSObj obj: pts) {
            //A里面有B里面没有
            if (!ptn.contains(obj)) {
                delta.addObject(obj);
                ptn.addObject(obj);
            }
        }
        if(!delta.isEmpty()){
            //foreach n → s ∈ PFG
            Set<Pointer> succsOfN = pointerFlowGraph.getSuccsOf(pointer);
            for(Pointer p: succsOfN){
                //add <s, pts> to WL
                workList.addEntry(p,delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        List<Invoke> invokes = recv.getVar().getInvokes();
        Context context = recv.getContext();
        for(Invoke invoke: invokes){
            JMethod jMethod = resolveCallee(recvObj,invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, jMethod);
            CSMethod calleeMethod = csManager.getCSMethod(calleeContext, jMethod);
            CSVar mthis = csManager.getCSVar(calleeContext, jMethod.getIR().getThis());
            workList.addEntry(mthis, PointsToSetFactory.make(recvObj));
            if(!callGraph.getCallersOf(calleeMethod).contains(csCallSite)){
                Edge<CSCallSite, CSMethod> edge = null;
                if(invoke.isSpecial())
                    edge = new Edge<>(CallKind.SPECIAL, csCallSite, calleeMethod);
                else if(invoke.isInterface())
                    edge = new Edge<>(CallKind.INTERFACE, csCallSite, calleeMethod);
                else if(invoke.isVirtual())
                    edge = new Edge<>(CallKind.VIRTUAL, csCallSite, calleeMethod);
                else if(invoke.isDynamic())
                    edge = new Edge<>(CallKind.DYNAMIC, csCallSite, calleeMethod);
                assert edge != null;
                callGraph.addEdge(edge);
                addReachable(calleeMethod);
                List<Var> actualParams = invoke.getInvokeExp().getArgs();
                List<Var> funcParams = jMethod.getIR().getParams();
                List<Var> returnVar = jMethod.getIR().getReturnVars();
                for(int i = 0; i < actualParams.size(); i ++){
                    addPFGEdge(csManager.getCSVar(context, actualParams.get(i)), csManager.getCSVar(calleeContext, funcParams.get(i)));
                }
                Var mret = invoke.getLValue();
                if(mret != null){
                    for (Var value : returnVar) {
                        addPFGEdge(csManager.getCSVar(calleeContext, value), csManager.getCSVar(context, mret));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
