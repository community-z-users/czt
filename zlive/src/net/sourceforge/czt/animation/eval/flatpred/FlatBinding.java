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
import java.util.logging.Logger;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZRefName;
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
    args = new ArrayList<ZRefName>();
    args.addAll(exprs);
    args.add(bind);
    solutionsReturned = -1;
  }

  /** Same modes as FlatTuple
   * TODO: move this code up to FlatPred
   */
  public Mode chooseMode(Envir env)
  {
    Mode m = modeFunction(env);
    if (m == null) {
      BitSet inputs = getInputs(env);
      double solutions = 0.0;
      if (inputs.get(args.size() - 1)) {
        solutions = 1.0;
        if (inputs.cardinality() > 1)
          solutions = 0.5;
        for (int i = 0; i < args.size() - 1; i++) {
          if (!inputs.get(i))
            env = env.add(args.get(i), null);
        }
        m = new Mode(env, inputs, solutions);
      }
    }
    return m;
  }

  /** Checks that the binding is an input, or ALL the other parameters are inputs. */
  private boolean assertInputArgs()
  {
    boolean result = evalMode_.isInput(args.size() - 1);
    if (!result) {
      result = true;
      for (int i = 0; result && i < args.size() - 1; i++)
        result = evalMode_.isInput(i);
    }
    return result;
  }

  public boolean nextEvaluation()
  {
    assert (evalMode_ != null);
    assert (solutionsReturned >= 0);
    assert (assertInputArgs());
    boolean result = false;
    if (solutionsReturned == 0) {
      //bindName contains the ZRefName which refers to the bind Expression in the env
      ZRefName bindName = args.get(args.size() - 1);

      solutionsReturned++;
      Envir env = evalMode_.getEnvir();

      //The case where the binding itself is an input
      if (evalMode_.isInput(args.size() - 1)) {
        BindExpr bindExpr = (BindExpr) env.lookup(bindName);
        List<Decl> bindingsList = bindExpr.getZDeclList().getDecl();
        //no. of elements in env.binding should be same as bindNames
        if (bindingsList.size() != bindNames.size())
          throw new CztException("Type error: bindings have sizes "
              +bindingsList.size()+" and "+bindNames.size());
        result = true;  // we start optimistic
        for (int i = 0; i < bindNames.size(); i++) {
          ZRefName exprName = args.get(i);
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
          ConstDecl cdecl = factory_.createConstDecl(bindNames.get(i), env.lookup(args.get(i)));
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
