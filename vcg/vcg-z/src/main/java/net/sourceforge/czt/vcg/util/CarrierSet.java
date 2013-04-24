/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 *
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.vcg.util;

import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.GenParamType;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdExpr;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchText;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.GenParamTypeVisitor;
import net.sourceforge.czt.z.visitor.GivenTypeVisitor;
import net.sourceforge.czt.z.visitor.PowerTypeVisitor;
import net.sourceforge.czt.z.visitor.ProdTypeVisitor;
import net.sourceforge.czt.z.visitor.SchemaTypeVisitor;
import net.sourceforge.czt.z.visitor.SignatureVisitor;

/**
 * Calculates the carrier set of types.
 */
public class CarrierSet
  implements
    TermVisitor<Term>,
    PowerTypeVisitor<Term>,
    GenParamTypeVisitor<Term>,
    GivenTypeVisitor<Term>,
    SchemaTypeVisitor<Term>,
    SignatureVisitor<Term>,
    ProdTypeVisitor<Term>
{
  protected Factory factory_;

  public CarrierSet()
  {
    this(new net.sourceforge.czt.z.util.Factory());
  }

  public CarrierSet(Factory zFactory)
  {
    if (zFactory == null)
      throw new IllegalArgumentException();
    factory_ = zFactory;
  }

  public Expr calculate(Dialect d, Type type) throws DefinitionException
  {
    try
    {
      return (Expr)type.accept(this);
    } catch(ClassCastException e)
    {
      throw new DefinitionException(d, type, "Could not calculate carrier set for type " + type);
    }
  }

  @Override
  public Term visitTerm(Term term)
  {
    return term;
  }

  /**
   * The carrier set of \power~T is the power expression
   * for the carrier set of T.
   */
  @Override
  public Term visitPowerType(PowerType powerType)
  {
    Type type = powerType.getType();
    Expr expr = (Expr) type.accept(this);
    PowerExpr result = factory_.createPowerExpr(expr);
    return result;
  }

  /**
   * The carrier set of \power~T is the power expression
   * for the carrier set of T.
   */
  @Override
  public Term visitGenParamType(GenParamType genParamType)
  {
    ZName genParamName = ZUtils.assertZName(genParamType.getName());
    ZName zName = factory_.createZName(genParamName);
    ZExprList zExprList = factory_.createZExprList();
    RefExpr result = factory_.createRefExpr(zName, zExprList, Boolean.FALSE);
    return result;
  }

  @Override
  public Term visitGivenType(GivenType givenType)
  {
    ZName givenTypeName = ZUtils.assertZName(givenType.getName());
    ZName zName = factory_.createZName(givenTypeName);
    ZExprList zExprList = factory_.createZExprList();
    RefExpr result = factory_.createRefExpr(zName, zExprList, Boolean.FALSE);
    return result;
  }

  @Override
  public Term visitSchemaType(SchemaType schemaType)
  {
    Signature signature = schemaType.getSignature();
    SchText schText = (SchText) signature.accept(this);
    SchExpr result = factory_.createSchExpr(schText);
    return result;
  }

  @Override
  public Term visitSignature(Signature signature)
  {
    List<NameTypePair> pairs = signature.getNameTypePair();
    List<Decl> decls = factory_.list();
    for (NameTypePair pair : pairs) {
      Expr expr = (Expr) pair.getType().accept(this);
      ZNameList zdnl = factory_.createZNameList();
      zdnl.add(pair.getName());
      VarDecl varDecl = factory_.createVarDecl(zdnl, expr);
      decls.add(varDecl);
    }
    ZDeclList zDeclList = factory_.createZDeclList(decls);
    ZSchText zSchText = factory_.createZSchText(zDeclList, null);
    return zSchText;
  }

  @Override
  public Term visitProdType(ProdType prodType)
  {
    List<Expr> exprs = factory_.list();
    List<Type2> types = prodType.getType();
    for (Iterator<Type2> iter = types.iterator(); iter.hasNext(); ) {
      Type type = iter.next();
      Expr expr = (Expr) type.accept(this);
      exprs.add(expr);
    }
    ZExprList zExprList = factory_.createZExprList(exprs);
    ProdExpr result = factory_.createProdExpr(zExprList);
    return result;
  }
}
