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
    TermVisitor,
    PowerTypeVisitor,
    GenParamTypeVisitor,
    GivenTypeVisitor,
    SchemaTypeVisitor,
    SignatureVisitor,
    ProdTypeVisitor,
    VariableTypeVisitor,
    VariableSignatureVisitor,
    UnknownTypeVisitor
{
  protected ZFactory zFactory_;

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
    zFactory_ = zFactory;
    allowVariableTypes_ = allowVariableTypes;
  }

  public Object visitTerm(Term term)
  {
    return term;
  }

  public Object visitPowerType(PowerType powerType)
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

  public Object visitGenParamType(GenParamType genParamType)
  {
    RefName refName =
      zFactory_.createRefName(genParamType.getName().getWord(),
                              genParamType.getName().getStroke(),
                              null);
    RefExpr result =
      zFactory_.createRefExpr(refName, list(), Boolean.FALSE);
    return result;
  }

  public Object visitGivenType(GivenType givenType)
  {
    RefName refName =
      zFactory_.createRefName(givenType.getName().getWord(),
                              givenType.getName().getStroke(),
                              null);
    RefExpr result =
      zFactory_.createRefExpr(refName, list(), Boolean.FALSE);
    return result;
  }

  public Object visitSchemaType(SchemaType schemaType)
  {
    Signature signature = schemaType.getSignature();
    SchText schText = (SchText) signature.accept(this);
    SchExpr result = zFactory_.createSchExpr(schText);
    return result;
  }

  public Object visitSignature(Signature signature)
  {
    List<NameTypePair> pairs = signature.getNameTypePair();
    List<Decl> decls = list();
    for (NameTypePair pair : pairs) {
      Expr expr = (Expr) pair.getType().accept(this);
      List<DeclName> name = list(pair.getName());
      VarDecl varDecl = zFactory_.createVarDecl(name, expr);
      decls.add(varDecl);
    }
    SchText schText = zFactory_.createSchText(decls, null);
    return schText;
  }

  public Object visitProdType(ProdType prodType)
  {
    List exprs = list();
    List types = prodType.getType();
    for (Iterator iter = types.iterator(); iter.hasNext(); ) {
      Type type = (Type) iter.next();
      Expr expr = (Expr) type.accept(this);
      exprs.add(expr);
    }

    ProdExpr result = zFactory_.createProdExpr(exprs);
    return result;
  }


  public Object visitUnknownType(UnknownType unknownType)
  {
    if (!allowVariableTypes_) {
      throw new UndeterminedTypeException();
    }
    RefName refName =
      zFactory_.createRefName(unknownType.toString(), list(), null);
    RefExpr result = zFactory_.createRefExpr(refName, list(), Boolean.FALSE);
    return result;
  }

  public Object visitVariableType(VariableType vType)
  {
    if (vType.getValue() instanceof VariableType) {
      if (!allowVariableTypes_) {
        throw new UndeterminedTypeException();
      }
      RefName refName =
        zFactory_.createRefName(vType.getName().getWord(),
                                vType.getName().getStroke(),
                                null);
      RefExpr result =
        zFactory_.createRefExpr(refName, list(), Boolean.FALSE);
      return result;
    }
    return vType.getValue().accept(this);
  }

  public Object visitVariableSignature(VariableSignature vSig)
  {
    if (vSig.getValue() instanceof VariableSignature) {
      throw new UndeterminedTypeException();
    }
    return vSig.getValue().accept(this);
  }

  protected List list()
  {
    return new ArrayList();
  }

  protected List list(Object o)
  {
    List list = list();
    list.add(o);
    return list;
  }
}
