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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import polyglot.lex.Operator;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
        //把这个方法的参数全部加进去，并把它们初始化为NAC
        List<Var> params = cfg.getIR().getParams();
        CPFact cpFact = new CPFact();
        //判断该变量是否是int类型
        for(Var var: params){
            if(ConstantPropagation.canHoldInt(var)){
                //update可以避免重复，就算重复了也可以正确覆盖掉
                //同时本身具有insert的功能
                cpFact.update(var,Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        //初始化为空
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        //把fact meet进target，对于target做操作
        //如果fact是空，不管
        if(fact.keySet() == null)
            return;
        //对于fact的key逐key做操作，如果target里面有，就meet然后update，否则直接copy进去（直接update）
        for(Var key : fact.keySet()){
            Value value = fact.get(key);
            //undef不代表缺失，说明有这个值，要更新
            //否则直接插入
            if(target.get(key) != Value.getUndef()) {
                value = meetValue(value, target.get(key));
            }
            target.update(key,value);
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC())
            return Value.getNAC();
        if(v1.isUndef())
            return Value.getUndef();
        //一定是一个常量
        //如果两个相等，那么就是这个数值
        if(v1.equals(v2))
            return Value.makeConstant(v1.getConstant());
        //如果两个不相等
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        //1.首先复制旧的in集合
        CPFact oldOut = out.copy();
//        if(out != null)
//            oldOut = out.copy();
        //2.然后合并in和out，把in merge进out
        meetInto(in, out);
        //首先判断是不是一个definitionStmt赋值语句,如果不是，那么直接不用管
        if(stmt instanceof DefinitionStmt){
            LValue lValue = ((DefinitionStmt<?, ?>) stmt).getLValue();
            //如果不是变量说明是其他语句，这个时候应该舍弃掉
            if(lValue != null && lValue instanceof Var && ConstantPropagation.canHoldInt((Var)lValue)) //不是null说明有左值要操作，否则不用操作out，直接恒等;同时还要判断左值是不是能为int
            {
                //获得左值
                Var var = (Var)lValue;
                //清除out里面原来x的值，即-{x,_}
                out.update(var, Value.getUndef());
                Exp exp = ((DefinitionStmt<?, ?>) stmt).getRValue();
                //获得该变量的新值并更新
                Value newVar = evaluate(exp,in);
                out.update(var,newVar);
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
        // TODO - finish me
        //x=c的常量情况
        if(exp instanceof IntLiteral)
            return Value.makeConstant(((IntLiteral) exp).getValue());
        //x=y的变量情况
        if(exp instanceof Var){
            //获得infact里面的该变量的值
            return in.get((Var)exp);
        }
        //x=y op z的二元表达式
        if(exp instanceof BinaryExp){
            Var y = ((BinaryExp) exp).getOperand1();
            Var z = ((BinaryExp) exp).getOperand2();
            //如果两个有一个不是intLike的，可以直接舍弃掉
            if(!ConstantPropagation.canHoldInt(y) || !ConstantPropagation.canHoldInt(z)){
                return Value.getUndef();
            }
            Value valY = in.get(y);
            Value valZ = in.get(z);
            //如果两个有一个是UNDEF那么也该是UNDEF
            if(valY.equals(Value.getUndef()) || valZ.equals(Value.getUndef()))
                return Value.getUndef();
            //如果有一个是NAC,返回NAC
            if(valY.equals(Value.getNAC()) || valZ.equals(Value.getNAC())){
                //其中如果是NAC除0的情况也是undef
                if(valY.equals(Value.getNAC()) && valZ.isConstant() && valZ.getConstant() == 0
                        && exp instanceof ArithmeticExp
                        && (((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.REM || ((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV))
                    return Value.getUndef();
                return Value.getNAC();
            }
            //根据不同的operator做不同的运算

            if(exp instanceof ArithmeticExp){
                ArithmeticExp.Op operator = ((ArithmeticExp) exp).getOperator();
                switch(operator){
                    case ADD:
                        return Value.makeConstant(valY.getConstant() + valZ.getConstant());
                    case SUB:
                        return Value.makeConstant(valY.getConstant() - valZ.getConstant());
                    case MUL:
                        return Value.makeConstant(valY.getConstant() * valZ.getConstant());
                    case DIV:
                        if(valZ.getConstant() == 0)
                            return Value.getUndef();
                        return Value.makeConstant(valY.getConstant() / valZ.getConstant());
                    case REM:
                        if(valZ.getConstant() == 0)
                            return Value.getUndef();
                        return Value.makeConstant(valY.getConstant() % valZ.getConstant());
                }
            }else if(exp instanceof ConditionExp){
                ConditionExp.Op operator = ((ConditionExp) exp).getOperator();
                return switch (operator) {
                    case EQ -> Value.makeConstant((valY.getConstant() == valZ.getConstant()) ? 1 : 0);
                    case GE -> Value.makeConstant((valY.getConstant() >= valZ.getConstant()) ? 1 : 0);
                    case GT -> Value.makeConstant((valY.getConstant() > valZ.getConstant()) ? 1 : 0);
                    case LE -> Value.makeConstant((valY.getConstant() <= valZ.getConstant()) ? 1 : 0);
                    case LT -> Value.makeConstant((valY.getConstant() < valZ.getConstant()) ? 1 : 0);
                    case NE -> Value.makeConstant((valY.getConstant() != valZ.getConstant()) ? 1 : 0);
                };
            }else if(exp instanceof ShiftExp){
                ShiftExp.Op operator = ((ShiftExp) exp).getOperator();
                return switch (operator){
                    case SHL -> Value.makeConstant(valY.getConstant() << valZ.getConstant());
                    case SHR -> Value.makeConstant(valY.getConstant() >> valZ.getConstant());
                    case USHR -> Value.makeConstant(valY.getConstant() >>> valZ.getConstant());
                };
            }else if(exp instanceof BitwiseExp){
                BitwiseExp.Op operator = ((BitwiseExp) exp).getOperator();
                return switch(operator){
                    case OR -> Value.makeConstant(valY.getConstant() | valZ.getConstant());
                    case AND -> Value.makeConstant(valY.getConstant() & valZ.getConstant());
                    case XOR -> Value.makeConstant(valY.getConstant() ^ valZ.getConstant());
                };
            }
            //二元表达式，但不在这些情况里面的，返回UNDEF
            return Value.getUndef();
        }
        //三种情况不能处理的，全部使用NAC来替代
        return Value.getNAC();
    }
}
