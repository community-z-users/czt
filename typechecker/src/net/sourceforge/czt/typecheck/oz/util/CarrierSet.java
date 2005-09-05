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
package net.sourceforge.czt.typecheck.oz.util;

import java.util.List;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.typecheck.z.util.UndeterminedTypeException;
import net.sourceforge.czt.typecheck.oz.impl.*;

/**
 * Calculates the carrier set of Object-Z types.
 */
public class CarrierSet
  extends net.sourceforge.czt.typecheck.z.util.CarrierSet
  implements
    ClassRefTypeVisitor<Term>,
    ClassUnionTypeVisitor<Term>,
    ClassPolyTypeVisitor<Term>,
    ClassRefVisitor<Term>,
    VariableClassTypeVisitor<Term>
{
  protected OzFactory ozFactory_;

  public CarrierSet()
  {
    super();
    ozFactory_ = new net.sourceforge.czt.oz.impl.OzFactoryImpl();
  }

  public CarrierSet(boolean allowVariableTypes)
  {
    this();
    allowVariableTypes_ = allowVariableTypes;
  }

  public CarrierSet(ZFactory zFactory, OzFactory ozFactory)
  {
    super(zFactory);
    ozFactory_ = ozFactory;
  }

  public Term visitClassRefType(ClassRefType classRefType)
  {
    ClassRef classRef = classRefType.getThisClass();
    Expr result = (Expr) classRef.accept(this);
    return result;
  }

  public Term visitClassPolyType(ClassPolyType classPolyType)
  {
    ClassRef classRef = classPolyType.getRootClass();
    Expr expr = (Expr) classRef.accept(this);
    PolyExpr result = ozFactory_.createPolyExpr(expr);
    return result;
  }

  public Term visitClassUnionType(ClassUnionType classUnionType)
  {
    ClassSig classSig = classUnionType.getClassSig();
    List<ClassRef> classRefs = classSig.getClasses();

    assert classRefs.size() != 1;
    Expr result = null;
    //if 0, then we have the set \oid
    if (classRefs.size() == 0) {
      RefName oidName =	ozFactory_.createRefName(OzString.OID,
						 GlobalDefs.<Stroke>list(),
						 null);
      result = ozFactory_.createRefExpr(oidName,
					GlobalDefs.<Expr>list(),
					Boolean.FALSE);
    }
    else {
      ClassUnionExpr classUnionExpr = null;
      for (ClassRef classRef : classRefs) {
        Expr expr = (Expr) classRef.accept(this);
        if (classUnionExpr == null) {
          classUnionExpr = ozFactory_.createClassUnionExpr();
          classUnionExpr.setLeftExpr(expr);
        }
        else if (classUnionExpr.getRightExpr() == null) {
          classUnionExpr.setRightExpr(expr);
        }
        else {
          ClassUnionExpr next =
            ozFactory_.createClassUnionExpr(classUnionExpr, expr);
          classUnionExpr = next;
        }
      }
      result = classUnionExpr;
      ParenAnn pAnn = ozFactory_.createParenAnn();
      result.getAnns().add(pAnn);
    }
    return result;
  }

  public Term visitClassRef(ClassRef classRef)
  {
    List<Expr> exprs = list();
    List<Type2> types = classRef.getType2();
    for (Type2 type : types) {
      Expr expr = (Expr) type.accept(this);
      exprs.add(expr);
    }
    Expr result =
      zFactory_.createRefExpr(classRef.getRefName(), exprs, Boolean.FALSE);
    if (classRef.getNameNamePair().size() > 0) {
      result = zFactory_.createRenameExpr(result, classRef.getNameNamePair());
    }
    return result;
  }

  public Term visitVariableClassType(VariableClassType vClassType)
  {
    Expr result = null;
    if (vClassType.getCandidateType() == null) {
      if (!allowVariableTypes_) {
        throw new UndeterminedTypeException();
      }
      RefName refName = zFactory_.createRefName("?CLASSTYPE?",
						GlobalDefs.<Stroke>list(),
						null);
      result = zFactory_.createRefExpr(refName,
				       GlobalDefs.<Expr>list(),
				       Boolean.FALSE);
    }
    else {
      Type2 type = vClassType.getCandidateType();
      vClassType.setValue(type);
      result = (Expr) type.accept(this);
    }
    return result;
  }
}
