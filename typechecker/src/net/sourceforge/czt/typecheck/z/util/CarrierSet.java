/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.z.util;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.typecheck.z.impl.*;

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
    ProdTypeVisitor<Term>,
    VariableTypeVisitor<Term>,
    VariableSignatureVisitor<Term>,
    UnknownTypeVisitor<Term>
{
  protected Factory factory_;
  protected net.sourceforge.czt.z.util.Factory zFactory_;

  /** Don't throw an exception when a variable type is encountered. */
  protected boolean allowVariableTypes_;

  public CarrierSet()
  {
    this(new net.sourceforge.czt.z.impl.ZFactoryImpl(), false);
  }

  public CarrierSet(boolean allowVariableTypes)
  {
    this(new net.sourceforge.czt.z.impl.ZFactoryImpl(), allowVariableTypes);
  }

  public CarrierSet(ZFactory zFactory)
  {
    this(zFactory, false);
  }

  public CarrierSet(ZFactory zFactory, boolean allowVariableTypes)
  {
    factory_ = new Factory(zFactory);
    zFactory_ = new  net.sourceforge.czt.z.util.Factory(zFactory);
    allowVariableTypes_ = allowVariableTypes;
  }

  public Term visitTerm(Term term)
  {
    return term;
  }

  public Term visitPowerType(PowerType powerType)
  {
    Type type = powerType.getType();

    //if the type is null, then the type is undefined
    if (type == null) {
      throw new UndeterminedTypeException();
    }

    Expr expr = (Expr) type.accept(this);
    PowerExpr result = zFactory_.createPowerExpr(expr);
    return result;
  }

  public Term visitGenParamType(GenParamType genParamType)
  {
    ZRefName zRefName =
      zFactory_.createZRefName(genParamType.getName().getWord(),
                               genParamType.getName().getStroke(),
                               null);
    ZExprList zExprList = zFactory_.createZExprList();
    RefExpr result =
      zFactory_.createRefExpr(zRefName, zExprList, Boolean.FALSE);
    return result;
  }

  public Term visitGivenType(GivenType givenType)
  {
    ZRefName zRefName =
      zFactory_.createZRefName(givenType.getName().getWord(),
			       givenType.getName().getStroke(),
                               null);
    ZExprList zExprList = zFactory_.createZExprList();
    RefExpr result =
      zFactory_.createRefExpr(zRefName, zExprList, Boolean.FALSE);
    return result;
  }

  public Term visitSchemaType(SchemaType schemaType)
  {
    Signature signature = schemaType.getSignature();
    SchText schText = (SchText) signature.accept(this);
    SchExpr result = zFactory_.createSchExpr(schText);
    return result;
  }

  public Term visitSignature(Signature signature)
  {
    List<NameTypePair> pairs = signature.getNameTypePair();
    List<Decl> decls = factory_.list();
    for (NameTypePair pair : pairs) {
      Expr expr = (Expr) pair.getType().accept(this);
      List<DeclName> name = factory_.list(pair.getDeclName());
      VarDecl varDecl = zFactory_.createVarDecl(name, expr);
      decls.add(varDecl);
    }
    ZDeclList zDeclList = zFactory_.createZDeclList(decls);
    ZSchText zSchText = zFactory_.createZSchText(zDeclList, null);
    return zSchText;
  }

  public Term visitProdType(ProdType prodType)
  {
    List<Expr> exprs = factory_.list();
    List<Type2> types = prodType.getType();
    for (Iterator iter = types.iterator(); iter.hasNext(); ) {
      Type type = (Type) iter.next();
      Expr expr = (Expr) type.accept(this);
      exprs.add(expr);
    }
    ZExprList zExprList = zFactory_.createZExprList(exprs);
    ProdExpr result = zFactory_.createProdExpr(zExprList);
    return result;
  }


  public Term visitUnknownType(UnknownType unknownType)
  {
    if (!allowVariableTypes_) {
      throw new UndeterminedTypeException();
    }
    List<Stroke> strokes = factory_.list();
    ZRefName zRefName =
      zFactory_.createZRefName("unknown(" + unknownType.getZRefName() + ")",
                               strokes, null);
    ZExprList zExprList = zFactory_.createZExprList();
    RefExpr result =
      zFactory_.createRefExpr(zRefName, zExprList, Boolean.FALSE);
    return result;
  }

  public Term visitVariableType(VariableType vType)
  {
    if (vType.getValue() == vType) {
      if (!allowVariableTypes_) {
        throw new UndeterminedTypeException();
      }
      List<Stroke> strokes = vType.getName().getStroke();
      ZRefName zRefName = zFactory_.createZRefName("??", strokes, null);
      ZExprList zExprList = zFactory_.createZExprList();
      RefExpr result =
        zFactory_.createRefExpr(zRefName, zExprList, Boolean.FALSE);
      return result;
    }
    return vType.getValue().accept(this);
  }

  public Term visitVariableSignature(VariableSignature vSig)
  {
    if (vSig.getValue() instanceof VariableSignature) {
      if (!allowVariableTypes_) {
        throw new UndeterminedTypeException();
      }
      List<Stroke> strokes = vSig.getName().getStroke();
      ZRefName zRefName =
        zFactory_.createZRefName("??", strokes, null);
      ZExprList zExprList = zFactory_.createZExprList();
      RefExpr refExpr =
        zFactory_.createRefExpr(zRefName, zExprList, Boolean.FALSE);
      InclDecl inclDecl = zFactory_.createInclDecl(refExpr);
      ZDeclList zDeclList =
        zFactory_.createZDeclList(factory_.<Decl>list(inclDecl));
      ZSchText result = zFactory_.createZSchText(zDeclList, null);
      return result;
    }
    return vSig.getValue().accept(this);
  }
}
