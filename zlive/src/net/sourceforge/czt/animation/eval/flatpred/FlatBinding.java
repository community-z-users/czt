/*
 * FlatBinding.java
 *
 * Created on 06 April 2005, 16:03
 */

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.logging.*;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;

/**
 * Originally as FlatTuple(B,b) implements (Elements of Map<RefName,Expr> B) = b
 *
 * Until updates on the structure of FlatPred.args, we need (Elements of ArrayList<ConstDecl> B).
 *
 * @author leo
 */
public class FlatBinding extends FlatPred {
    
    private static final Logger sLogger
    = Logger.getLogger("net.sourceforge.czt.animation.eval");

    protected Factory factory_ = new Factory();
    
    /** Creates a new instance of FlatBinding
        @obsolete
    public FlatBinding(RefName bind, NameExprPair... bindings) {
        this(Arrays.asList(bindings), bind);
    }
    */
    
    public FlatBinding(ZDeclList bindings, RefName bind)
    {
        sLogger.entering("FlatBinding","FlatBinding");
        HashSet names = new HashSet();
        for(Decl decl : bindings.getDecl()) {
          ConstDecl constDecl = (ConstDecl) decl;
          sLogger.fine("name/expr = "+constDecl.getDeclName()
                       +"/"+constDecl.getExpr());
          if (!names.add(constDecl.getDeclName()))
            throw new IllegalArgumentException("FlatBinding requires that given list of name-expr pairs has no duplicates");
        }
        args = new ArrayList(bindings.getDecl());
        args.add(bind);
        solutionsReturned = -1;
        sLogger.exiting("FlatBinding","FlatBinding");
    }
    
    //@ requires newargs.size() >= 1;
    /** @obsolete
    public FlatBinding(List<NameExprPair> newargs) {
        this(newargs.subList(0,newargs.size()-1),(RefName)newargs.get(newargs.size()-1));
    }
    */

    // same as FlatTuple
    public Mode chooseMode(Envir env) {
        Mode m = modeFunction(env);
        if (m == null) {
            ArrayList inputs = new ArrayList(args.size());
            int varsDefined = setInputs(env, inputs);
            double solutions = 0.0;
            if (((Boolean)inputs.get(inputs.size()-1)).booleanValue()) {
                solutions = 1.0;
                if (varsDefined > 1)
                    solutions = 0.5;
                for(int i=0;i<args.size()-1;i++) {
                    if (((Boolean)inputs.get(i)).booleanValue() == false)
                        env = env.add((RefName)args.get(i),null);
                }
                m = new Mode(env, inputs, solutions);
            }
        }
        return m;
    }
    
    private boolean assertInputArgs() {
        boolean result = evalMode_.isInput(args.size()-1);
        if(!result) {
            result = true;
            for (int i=0;result && i<args.size()-1;i++)
                result = evalMode_.isInput(i);
        }
        return result;
    }
    
    public boolean nextEvaluation() {
        assert (evalMode_ != null);
        assert (solutionsReturned >= 0);
        assert (assertInputArgs());
        boolean result = false;        
        if(solutionsReturned==0) {
            //bindName contains the RefName which refers to the bind Expression in the env
            RefName bindName = (RefName)args.get(args.size()-1);
            
            solutionsReturned++;
            
            //The case where the bind itself is an input
            if(evalMode_.isInput(args.size()-1)) {
                BindExpr bindExpr = (BindExpr)evalMode_.getEnvir().lookup(bindName);                
                List bindingsList = ((ZDeclList) bindExpr.getDeclList()).getDecl();
                //no. of elements in env.binding should be same as that passed as inputs
                if(bindingsList.size() == args.size()-1) {
                    boolean flag = true;
                    for(int i=0;i<bindingsList.size();i++) {
                        //if a RefName is not in the env, then it is set seeing the value in env.bindings
                        ConstDecl constDecl = (ConstDecl)args.get(i);                        
                        RefName bindElemName = factory_.createRefName(constDecl.getDeclName());
                        if(evalMode_.getEnvir().lookup(bindElemName) == null) {
                            evalMode_.getEnvir().setValue(bindElemName, constDecl.getExpr());
                        }
                        //if a RefName is there in the env, it is checked to be equal to the corresponsing one in env.bindings
                        else {
                            if(!(evalMode_.getEnvir().lookup(bindElemName).equals(constDecl.getExpr())))
                                flag = false;
                        }
                    }
                    //the result is set to false even if one of the RefNames differs in the env.tuple and in the inputs
                    result = flag;
                }
            }
            //In case the tuple is not defined in the env, a new tuple is formed and added to the env
            else {
                result = true;
                List exprList = new ArrayList(args.size()-1);
                for(int i=0;i<args.size()-1;i++) {
                    ConstDecl constDecl = (ConstDecl)args.get(i);
                    RefName bindElemName = factory_.createRefName(constDecl.getDeclName());
                    exprList.add(evalMode_.getEnvir().lookup(bindElemName));
                }
                Expr bindExpr =
                  factory_.createBindExpr(factory_.createZDeclList(exprList));
                evalMode_.getEnvir().setValue(bindName, bindExpr);
            }
        }
        return result;
    }
    
    ///////////////////////// Pred methods ///////////////////////
    
    public Object accept(Visitor visitor) {
        if (visitor instanceof FlatBindingVisitor) {
            FlatBindingVisitor flatBindingVisitor = (FlatBindingVisitor) visitor;
            return flatBindingVisitor.visitFlatBinding(this);
        }
        return super.accept(visitor);
    }
}
