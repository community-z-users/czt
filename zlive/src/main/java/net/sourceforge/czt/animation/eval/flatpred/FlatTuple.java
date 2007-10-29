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

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatTupleVisitor;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/**
* @author Mark Utting
*
* FlatTuple(A,t) implements (Elements of ArrayList A) = t
*/
public class FlatTuple extends FlatPred
{
  protected Factory factory_ = new Factory();

  public FlatTuple(List<ZName> elements, ZName tuple)
  {
    args_ = new ArrayList<ZName>(elements);
    args_.add(tuple);
    solutionsReturned_ = -1;
  }

  //@ requires newargs.size() >= 1;
  public FlatTuple(List<ZName> newargs)
  {
    this(newargs.subList(0,newargs.size()-1),newargs.get(newargs.size()-1));
  }

  /* (non-Javadoc)
   * @see net.sourceforge.czt.animation.eval.flatpred.FlatPred#inferBounds(net.sourceforge.czt.animation.eval.flatpred.Bounds)
   */
  @Override
  public boolean inferBounds(Bounds bnds)
  {
    for (int i=0; i< args_.size()-1; i++) {
      bnds.addStructureArg(getLastArg(), Integer.valueOf(i+1), args_.get(i));
    }
    return false;
  }

  /** Same modes as FlatBinding */
  public Mode chooseMode(Envir env)
  {
    return modeCollection(env);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert (evalMode_ != null);
    assert (solutionsReturned_ >= 0);
    // @czt.todo package these assertions into a separate function.
    if(!evalMode_.isInput(args_.size()-1)) {
      for (int i=0;i<args_.size()-1;i++)
        assert (evalMode_.isInput(i));
    }
    boolean result = false;
    //tupleName contains the ZName which refers to the tuple Expression in the env
    ZName tupleName = args_.get(args_.size()-1);
    if(solutionsReturned_==0) {
      solutionsReturned_++;
      //The case where the tuple itself is an input
      if(evalMode_.isInput(args_.size()-1)) {
        Expr tupleExpr = evalMode_.getEnvir().lookup(tupleName);
        List<Expr> memberList = ((TupleExpr)tupleExpr).getZExprList();
        //no. of elements in env.tuple should be same as that passed as inputs
        if(memberList.size() == args_.size()-1) {
          boolean flag = true;
          for(int i=0;i<memberList.size();i++) {
	    ZName elem = args_.get(i);
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
        for(int i=0;i<args_.size()-1;i++)
          exprList.add(evalMode_.getEnvir().lookup(args_.get(i)));
        Expr tupleExpr = factory_.createTupleExpr(exprList);
        evalMode_.getEnvir().setValue(tupleName,tupleExpr);
      }
    }
    return result;
  }


  ///////////////////////// Pred methods ///////////////////////

  @Override
  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append(printLastArg());
    result.append(" = (");
    for (int i=0; i < args_.size() - 1; i++) {
      result.append(printArg(i));
      if (i < args_.size() - 2)
        result.append(", ");
    }
    result.append(")");
    return result.toString();
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatTupleVisitor)
      return ((FlatTupleVisitor<R>) visitor).visitFlatTuple(this);
    else
      return super.accept(visitor);
  }
}
