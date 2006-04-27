/**
Copyright (C) 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.List;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.util.CztException;
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
 * @author marku  (Rewrote nextEvaluation, 3 Feb 2006)
 */
public class FlatBinding extends FlatPred
{
  protected Factory factory_ = new Factory();

  private List<ZDeclName> bindNames;

  /** Constructs a FlatBinding FlatPred.
   @param names The list of names in the binding (name1,name2,...nameN). (no duplicates)
   @param exprs The list of expressions (e1,e2,...,eN).
   @param bind  The name of the BindExpr \lblot name1==e1, ... nameN==eN \rblot.
   */
  public FlatBinding(List<ZDeclName> names, List<ZRefName> exprs,
      ZRefName bind)
  {
    assert names.size() == exprs.size();

    if ((new HashSet<ZDeclName>(names)).size() != names.size())
      throw new IllegalArgumentException(
          "FlatBinding contains duplicate names: " + names);

    bindNames = names;
    args_ = new ArrayList<ZRefName>();
    args_.addAll(exprs);
    args_.add(bind);
    solutionsReturned_ = -1;
  }

  /** Same modes as FlatTuple */
  public Mode chooseMode(Envir env)
  {
    return modeCollection(env);
  }

  /** Checks that the binding is an input, or ALL the other parameters are inputs. */
  private boolean assertInputArgs()
  {
    boolean result = evalMode_.isInput(args_.size() - 1);
    if (!result) {
      result = true;
      for (int i = 0; result && i < args_.size() - 1; i++)
        result = evalMode_.isInput(i);
    }
    return result;
  }

  public boolean nextEvaluation()
  {
    assert (evalMode_ != null);
    assert (solutionsReturned_ >= 0);
    assert (assertInputArgs());
    boolean result = false;
    if (solutionsReturned_ == 0) {
      //bindName contains the ZRefName which refers to the bind Expression in the env
      ZRefName bindName = args_.get(args_.size() - 1);

      solutionsReturned_++;
      Envir env = evalMode_.getEnvir();

      //The case where the binding itself is an input
      if (evalMode_.isInput(args_.size() - 1)) {
        BindExpr bindExpr = (BindExpr) env.lookup(bindName);
        List<Decl> bindingsList = bindExpr.getZDeclList().getDecl();
        //no. of elements in env.binding should be same as bindNames
        if (bindingsList.size() != bindNames.size())
          throw new CztException("Type error: bindings have sizes "
              +bindingsList.size()+" and "+bindNames.size());
        result = true;  // we start optimistic
        for (int i = 0; i < bindNames.size(); i++) {
          ZRefName exprName = args_.get(i);
          ZDeclName boundName = bindNames.get(i);
          // find the corresponding boundName in bindingsList
          // TODO: this is O(N^2) in the length of the binding lists.
          //       It would be more efficient to sort both lists first,
          //       then do one pass over them.
          ConstDecl cdecl = null;
          for (Decl decl : bindingsList) {
            if (((ConstDecl)decl).getDeclName().equals(boundName)) {
              cdecl = (ConstDecl) decl;
              break;
            }
          }
          if (cdecl == null)
            throw new CztException("Type error: binding does not contain: "+boundName);
          //if exprName is not in the env, then it is set using the value in env.bindings
          if (env.lookup(exprName) == null)
              env.setValue(exprName, cdecl.getExpr());
          else
            // check that the two values are equal
            if ( ! env.lookup(exprName).equals(cdecl.getExpr()))
              result = false;
          }
        }
      else {
        // create a new binding and add it to the env
        result = true;
        List<Decl> declList = new ArrayList<Decl>(bindNames.size());
        for (int i = 0; i < bindNames.size(); i++) {
          ConstDecl cdecl = factory_.createConstDecl(bindNames.get(i), env.lookup(args_.get(i)));
          declList.add(cdecl);
        }
        Expr bindExpr = factory_.createBindExpr(factory_.createZDeclList(declList));
        env.setValue(bindName, bindExpr);
      }
    }
    return result;
  }

  ///////////////////////// Pred methods ///////////////////////

  public Object accept(Visitor visitor)
  {
    if (visitor instanceof FlatBindingVisitor) {
      FlatBindingVisitor flatBindingVisitor = (FlatBindingVisitor) visitor;
      return flatBindingVisitor.visitFlatBinding(this);
    }
    return super.accept(visitor);
  }
}
