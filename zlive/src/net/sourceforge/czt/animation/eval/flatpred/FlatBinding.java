/*
 * FlatBinding.java
 *
 * Created on 06 April 2005, 16:03
 */

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.logging.*;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;

/**
 * Evaluates ZBinding terms.
 * It implements <| name1==e1, name2==e2, ... nameN==eN |> = bind.
 * Note that this is similar to the theta operator in Z, which
 * explodes bind (a ZBinding term) into a set of names and expressions.
 *
 * @author leo
 */
public class FlatBinding extends FlatPred {
    
  private static final Logger sLogger
    = Logger.getLogger("net.sourceforge.czt.animation.eval");

  protected Factory factory_ = new Factory();

  private List<ZDeclName> bindNames;
  
  /** Constructs a FlatBinding FlatPred.
      @param names The list of names in the binding (name1,name2,...nameN).
      @param exprs The list of expressions (e1,e2,...,eN).
      @param bind  The ZBinding term that contains names and exprs.
  */
  public FlatBinding(List<ZDeclName> names,
		     List<ZRefName> exprs, 
		     ZRefName bind)
  {
    sLogger.entering("FlatBinding","FlatBinding");
    assert names.size() == exprs.size();

    if ((new HashSet<ZDeclName>(names)).size() != names.size())
      throw new IllegalArgumentException("FlatBinding contains duplicate names: " + names);

    bindNames = names;
    args = new ArrayList<ZRefName>();
    args.addAll(exprs);
    args.add(bind);
    solutionsReturned = -1;
    sLogger.exiting("FlatBinding","FlatBinding");
  }
    

  /** Same modes as FlatTuple */
  public Mode chooseMode(Envir env) {
    Mode m = modeFunction(env);
    if (m == null) {
      BitSet inputs = getInputs(env);
      double solutions = 0.0;
      if (inputs.get(args.size()-1)) {
	solutions = 1.0;
	if (inputs.cardinality() > 1)
	  solutions = 0.5;
	for(int i=0;i<args.size()-1;i++) {
	  if ( ! inputs.get(i))
	    env = env.add(args.get(i),null);
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
            //bindName contains the ZRefName which refers to the bind Expression in the env
            ZRefName bindName = args.get(args.size()-1);
            
            solutionsReturned++;
            
            //The case where the bind itself is an input
            if(evalMode_.isInput(args.size()-1)) {
                BindExpr bindExpr = (BindExpr)evalMode_.getEnvir().lookup(bindName);                
                List bindingsList = ((ZDeclList) bindExpr.getDeclList()).getDecl();
                //no. of elements in env.binding should be same as that passed as inputs
                if(bindingsList.size() == args.size()-1) {
                    boolean flag = true;
                    for(int i=0;i<bindingsList.size();i++) {
                        //if a ZRefName is not in the env, then it is set seeing the value in env.bindings
                        ConstDecl constDecl = (ConstDecl)args.get(i);                        
                        ZRefName bindElemName = factory_.createZRefName(constDecl.getZDeclName());
                        if(evalMode_.getEnvir().lookup(bindElemName) == null) {
                            evalMode_.getEnvir().setValue(bindElemName, constDecl.getExpr());
                        }
                        //if a ZRefName is there in the env, it is checked to be equal to the corresponsing one in env.bindings
                        else {
                            if(!(evalMode_.getEnvir().lookup(bindElemName).equals(constDecl.getExpr())))
                                flag = false;
                        }
                    }
                    //the result is set to false even if one of the ZRefNames differs in the env.tuple and in the inputs
                    result = flag;
                }
            }
            //In case the tuple is not defined in the env, a new tuple is formed and added to the env
            else {
                result = true;
                List exprList = new ArrayList(args.size()-1);
                for(int i=0;i<args.size()-1;i++) {
                    ConstDecl constDecl = (ConstDecl)args.get(i);
                    ZRefName bindElemName = factory_.createZRefName(constDecl.getZDeclName());
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
