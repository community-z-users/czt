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
* FlatCard(A,s) implements Size of Set A = s
*/
public class FlatCard
  extends FlatPred
{
  protected Factory factory_ = new Factory();
  //protected ArrayList vars_ = new ArrayList();

  public FlatCard(RefName set, RefName size)
  {
    args = new ArrayList(2);
    args.add(set);
    args.add(size);
    solutionsReturned = -1;
  }

  //@ requires newargs.size() == 2;
  public FlatCard(ArrayList newargs)
  {
    if (newargs == null || newargs.size() != 2)
      throw new IllegalArgumentException("FlatCard requires 2 args");
    args = newargs;
    solutionsReturned = -1;
  }

  /** Chooses the mode in which the predicate can be evaluated.*/
  public Mode chooseMode(/*@non_null@*/ Envir env)
  {
    return modeFunction(env);
  }

  /** Does the actual evaluation */
  public boolean nextEvaluation()
  {
    assert evalMode_ != null;
    assert solutionsReturned >= 0;
    assert evalMode_.isInput(0);
    boolean result = false;
    RefName set = (RefName)args.get(0);
    assert (set instanceof EvalSet);
    if(solutionsReturned==0)
    {
      solutionsReturned++;
      Iterator it = ((EvalSet)evalMode_.getEnvir().lookup(set)).members();
      BigInteger i = new BigInteger("0");
      while(it.hasNext()) {
        it.next();
        i = i.add(BigInteger.ONE);
      }
      Expr size = factory_.createNumExpr(i);
      if (evalMode_.isInput(1)) {
        Expr thisSize = evalMode_.getEnvir().lookup((RefName)args.get(1));
        if(thisSize.equals(size))
          result = true;
      }
      else {
        // assign this object (an EvalSet) to the output variable.
        evalMode_.getEnvir().setValue((RefName)args.get(1),size);
        result = true;
      }
    }
    return result;
  }

  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatCardVisitor) {
      FlatCardVisitor flatCardVisitor = (FlatCardVisitor) visitor;
      return flatCardVisitor.visitFlatCard(this);
    }
    return super.accept(visitor);
  }
}
