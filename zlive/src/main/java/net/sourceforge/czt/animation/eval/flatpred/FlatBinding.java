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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.animation.eval.ZRefNameComparator;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.PrintVisitor;

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

  private List<ZName> bindNames;

  /** Used for converting ZNames into strings. */
  private PrintVisitor namePrinter = new PrintVisitor(false);

  /** Constructs a FlatBinding FlatPred.
   @param names The list of names in the binding (name1,name2,...nameN). (no duplicates)
   @param exprs The list of expressions (e1,e2,...,eN).
   @param bind  The name of the BindExpr \lblot name1==e1, ... nameN==eN \rblot.
   */
  public FlatBinding(List<ZName> names, List<ZName> exprs,
      ZName bind)
  {
    assert names.size() == exprs.size();

    if ((new HashSet<ZName>(names)).size() != names.size())
      throw new IllegalArgumentException(
          "FlatBinding contains duplicate names: " + names);

    bindNames = names;
    args_ = new ArrayList<ZName>();
    args_.addAll(exprs);
    // we sort the names to ensure a consistent order in all bindings
    // that we create.
    Collections.sort(args_, ZRefNameComparator.create());
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
    boolean result = evalMode_.isInput(getLastArg());
    if (!result) {
      result = true;
      for (int i = 0; result && i < args_.size() - 1; i++)
        result = evalMode_.isInput(args_.get(i));
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
      //bindName contains the ZName which refers to the bind Expression in the env
      ZName bindName = args_.get(args_.size() - 1);

      solutionsReturned_++;
      Envir env = evalMode_.getEnvir();

      //The case where the binding itself is an input
      if (evalMode_.isInput(getLastArg())) {
        BindExpr bindExpr = (BindExpr) env.lookup(bindName);
        List<Decl> bindingsList = bindExpr.getZDeclList();
        //no. of elements in env.binding should be same as bindNames
        if (bindingsList.size() != bindNames.size())
          throw new CztException("Type error: bindings have sizes "
              +bindingsList.size()+" and "+bindNames.size());
        result = true;  // we start optimistic
        // the names in both bindings should be sorted, so we do one 
        // sequential pass, checking the names and comparing values.
        for (int i = 0; i < bindNames.size(); i++) {
          ZName boundName = bindNames.get(i);
          String boundNameStr = boundName.accept(namePrinter);
          ConstDecl cdecl = (ConstDecl) bindingsList.get(i);
          String name = cdecl.getName().accept(namePrinter);
          assert name.equals(boundNameStr)
              : "binding names are not equal/sorted: "+name+"/="+boundNameStr;
          // now set cdecl in the environment or compare its value
          ZName exprName = args_.get(i);
          if (env.lookup(exprName) == null)
              env.setValue(exprName, cdecl.getExpr());
          else
            // check that the two values are equal
            if ( ! ExprComparator.equalZ(env.lookup(exprName),cdecl.getExpr()))
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

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof FlatBindingVisitor)
      return ((FlatBindingVisitor<R>) visitor).visitFlatBinding(this);
    else
      return super.accept(visitor);
  }
}
