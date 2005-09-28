/**
Copyright (C) 2004 Mark Utting
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.*;
import java.math.*;

import net.sourceforge.czt.util.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.impl.TermAImpl;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.animation.eval.*;

/**
* @author Mark Utting
*
* FlatTuple(A,t) implements (Elements of ArrayList A) = t
*/
public class FlatTuple extends FlatPred
{
  protected Factory factory_ = new Factory();
  
  public FlatTuple(List<ZRefName> elements, ZRefName tuple)
  {
    args = new ArrayList<ZRefName>(elements);
    args.add(tuple);
    solutionsReturned = -1;
  }
  
  //@ requires newargs.size() >= 1;
  public FlatTuple(List<ZRefName> newargs)
  {
    this(newargs.subList(0,newargs.size()-1),newargs.get(newargs.size()-1));
  }
  
  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
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
  
  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert (evalMode_ != null);
    assert (solutionsReturned >= 0);
    // @czt.todo package these assertions into a separate function.
    if(!evalMode_.isInput(args.size()-1)) {
      for (int i=0;i<args.size()-1;i++) 
        assert (evalMode_.isInput(i));
    }
    boolean result = false;
    //tupleName contains the ZRefName which refers to the tuple Expression in the env
    ZRefName tupleName = args.get(args.size()-1);
    if(solutionsReturned==0) {
      solutionsReturned++;
      //The case where the tuple itself is an input
      if(evalMode_.isInput(args.size()-1)) {
        Expr tupleExpr = evalMode_.getEnvir().lookup(tupleName);
        List<Expr> memberList = ((TupleExpr)tupleExpr).getZExprList();
        //no. of elements in env.tuple should be same as that passed as inputs
        if(memberList.size() == args.size()-1) {
          boolean flag = true;
          for(int i=0;i<memberList.size();i++) {
	    ZRefName elem = args.get(i);
	    Object value = evalMode_.getEnvir().lookup(elem);
            //if value of elem is unknown (null), we do envir(elem) := value from tuple
            if(value == null) {
              evalMode_.getEnvir().setValue(elem, memberList.get(i));
            }
            else {
              // value is known, so check it is equal to value in tuple
              if ( ! (value.equals(memberList.get(i))))
                flag = false;
            }
          }
          // result is true iff envir now contains the same values as the tuple
	  //  (for the variables that appear in the tuple)
          result = flag;
        }
      }
      //In case the tuple is not defined in the env, a new tuple is formed and added to the env
      else {
        result = true;
        ZExprList exprList = factory_.createZExprList();
        for(int i=0;i<args.size()-1;i++)
          exprList.add(evalMode_.getEnvir().lookup(args.get(i)));
        Expr tupleExpr = factory_.createTupleExpr(exprList);
        evalMode_.getEnvir().setValue(tupleName,tupleExpr);
      }
    }
    return result;
  }
  
  ///////////////////////// Pred methods ///////////////////////
  
  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatTupleVisitor) {
      FlatTupleVisitor flatTupleVisitor = (FlatTupleVisitor) visitor;
      return flatTupleVisitor.visitFlatTuple(this);
    }
    return super.accept(visitor);
  }
}
