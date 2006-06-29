/*
  Copyright (C) 2005 Petra Malik
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

package net.sourceforge.czt.rules.ast;

import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.impl.ZpattFactoryImpl;

/**
 * Makes sure that Joker are only created once.
 *
 * @author Petra Malik
 */
public class ProverFactory
  extends ZpattFactoryImpl
{
  private Map<String, ProverJokerDeclList> mJokerDeclLists_ =
    new HashMap<String, ProverJokerDeclList>();
  private Map<String, ProverJokerExprList> mJokerExprLists_ =
    new HashMap<String, ProverJokerExprList>();
  private Map<String, ProverJokerPred> mJokerPreds_ =
    new HashMap<String, ProverJokerPred>();
  private Map<String, ProverJokerExpr> mJokerExprs_ =
    new HashMap<String, ProverJokerExpr>();
  private Map<String, ProverJokerDeclName> mJokerDeclNames_ =
    new HashMap<String, ProverJokerDeclName>();
  private Map<String, ProverJokerRefName> mJokerRefNames_ =
    new HashMap<String, ProverJokerRefName>();

  /**
   * Throws an UnsupportedOperationException.
   */
  public JokerDeclList createJokerDeclList()
  {
    throw new UnsupportedOperationException();
  }

  public JokerDeclList createJokerDeclList(String name)
  {
    ProverJokerDeclList result = mJokerDeclLists_.get(name);
    if (result == null) {
      result = new  ProverJokerDeclList(name);
      mJokerDeclLists_.put(name, result);
    }
    return result;
  }

  public JokerDeclListBinding createJokerDeclListBinding()
  {
    String message =
      "The JokerDeclList for the new JokerDeclListBinding must be given";
    throw new UnsupportedOperationException(message);
  }

  public JokerDeclListBinding createJokerDeclListBinding(JokerDeclList binding,
    Decl vDecl)
  {
    String name = binding.getName();
    ProverJokerDeclList joker = mJokerDeclLists_.get(name);
    if (joker == null) {
      throw new IllegalArgumentException("Unknown joker " + name);
    }
    return joker.getBinding();
  }

  /**
   * Throws an UnsupportedOperationException.
   */
  public JokerExprList createJokerExprList()
  {
    throw new UnsupportedOperationException();
  }

  public JokerExprList createJokerExprList(String name)
  {
    ProverJokerExprList result = mJokerExprLists_.get(name);
    if (result == null) {
      result = new  ProverJokerExprList(name);
      mJokerExprLists_.put(name, result);
    }
    return result;
  }

  public JokerExprListBinding createJokerExprListBinding()
  {
    String message =
      "The JokerExprList for the new JokerExprListBinding must be given";
    throw new UnsupportedOperationException(message);
  }

  public JokerExprListBinding createJokerExprListBinding(JokerExprList binding,
    Expr vExpr)
  {
    String name = binding.getName();
    ProverJokerExprList joker = mJokerExprLists_.get(name);
    if (joker == null) {
      throw new IllegalArgumentException("Unknown joker " + name);
    }
    return joker.getBinding();
  }

  /**
   * Throws an UnsupportedOperationException.
   */
  public JokerPred createJokerPred()
  {
    throw new UnsupportedOperationException();
  }

  public JokerPred createJokerPred(String name)
  {
    ProverJokerPred result = mJokerPreds_.get(name);
    if (result == null) {
      result = new  ProverJokerPred(name);
      mJokerPreds_.put(name, result);
    }
    return result;
  }

  public JokerPredBinding createJokerPredBinding()
  {
    String message =
      "The JokerPred for the new JokerPredBinding must be given";
    throw new UnsupportedOperationException(message);
  }

  public JokerPredBinding createJokerPredBinding(JokerPred binding,
    Pred vPred)
  {
    String name = binding.getName();
    ProverJokerPred joker = mJokerPreds_.get(name);
    if (joker == null) {
      throw new IllegalArgumentException("Unknown joker " + name);
    }
    return joker.getBinding();
  }

  /**
   * Throws an UnsupportedOperationException.
   */
  public JokerExpr createJokerExpr()
  {
    throw new UnsupportedOperationException();
  }

  public JokerExpr createJokerExpr(String name)
  {
    ProverJokerExpr result = mJokerExprs_.get(name);
    if (result == null) {
      result = new  ProverJokerExpr(name);
      mJokerExprs_.put(name, result);
    }
    return result;
  }

  public JokerExprBinding createJokerExprBinding()
  {
    String message =
      "The JokerExpr for the new JokerExprBinding must be given";
    throw new UnsupportedOperationException(message);
  }

  public JokerExprBinding createJokerExprBinding(JokerExpr binding,
    Expr vExpr)
  {
    String name = binding.getName();
    ProverJokerExpr joker = mJokerExprs_.get(name);
    if (joker == null) {
      throw new IllegalArgumentException("Unknown joker " + name);
    }
    return joker.getBinding();
  }

  /**
   * Throws an UnsupportedOperationException.
   */
  public JokerDeclName createJokerDeclName()
  {
    throw new UnsupportedOperationException();
  }

  public JokerDeclName createJokerDeclName(String name)
  {
    ProverJokerDeclName result = mJokerDeclNames_.get(name);
    if (result == null) {
      result = new  ProverJokerDeclName(name);
      mJokerDeclNames_.put(name, result);
      ProverJokerRefName jokerRefName = new ProverJokerRefName(name);
      mJokerRefNames_.put(name, jokerRefName);
      result.setJokerRefName(jokerRefName);
      jokerRefName.setJokerDeclName(result);
    }
    return result;
  }

  public JokerDeclNameBinding createJokerDeclNameBinding()
  {
    String message =
      "The JokerDeclName for the new JokerDeclNameBinding must be given";
    throw new UnsupportedOperationException(message);
  }

  public JokerDeclNameBinding createJokerDeclNameBinding(JokerDeclName binding,
    DeclName vDeclName)
  {
    String name = binding.getName();
    ProverJokerDeclName joker = mJokerDeclNames_.get(name);
    if (joker == null) {
      throw new IllegalArgumentException("Unknown joker " + name);
    }
    return joker.getBinding();
  }

  /**
   * Throws an UnsupportedOperationException.
   */
  public JokerRefName createJokerRefName()
  {
    throw new UnsupportedOperationException();
  }

  public JokerRefName createJokerRefName(String name)
  {
    ProverJokerRefName result = mJokerRefNames_.get(name);
    if (result == null) {
      result = new  ProverJokerRefName(name);
      mJokerRefNames_.put(name, result);
      ProverJokerDeclName jokerDeclName = new ProverJokerDeclName(name);
      mJokerDeclNames_.put(name, jokerDeclName);
      result.setJokerDeclName(jokerDeclName);
      jokerDeclName.setJokerRefName(result);
    }
    return result;
  }

  public JokerRefNameBinding createJokerRefNameBinding()
  {
    String message =
      "The JokerRefName for the new JokerRefNameBinding must be given";
    throw new UnsupportedOperationException(message);
  }

  public JokerRefNameBinding createJokerRefNameBinding(JokerRefName binding,
    RefName vRefName)
  {
    String name = binding.getName();
    ProverJokerRefName joker = mJokerRefNames_.get(name);
    if (joker == null) {
      throw new IllegalArgumentException("Unknown joker " + name);
    }
    return joker.getBinding();
  }


  public LookupConstDeclProviso
  createLookupConstDeclProviso(SequentContext sequentContext,
                               Expr leftExpr,
                               Expr rightExpr)
  {
    LookupConstDeclProviso proviso = new ProverLookupConstDeclProviso();
    proviso.setSequentContext(sequentContext);
    proviso.setLeftExpr(leftExpr);
    proviso.setRightExpr(rightExpr);
    return proviso;
  }

  public CalculateProviso
  createCalculateProviso(SequentContext sequentContext,
                         Expr leftExpr,
                         Expr rightExpr)
  {
    CalculateProviso proviso = new ProverCalculateProviso();
    proviso.setSequentContext(sequentContext);
    proviso.setLeftExpr(leftExpr);
    proviso.setRightExpr(rightExpr);
    return proviso;
  }

  public TypeProviso
  createTypeProviso(SequentContext sequentContext,
                    Expr expr,
                    Expr type)
  {
    TypeProviso proviso = new ProverTypeProviso();
    proviso.setSequentContext(sequentContext);
    proviso.setExpr(expr);
    proviso.setType(type);
    return proviso;
  }
}
