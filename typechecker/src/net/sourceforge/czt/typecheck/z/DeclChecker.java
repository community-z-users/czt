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
package net.sourceforge.czt.typecheck.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 * A <code>DeclChecker</code> instance visits the Decl instances in an
 * AST, checks the preds for type consistencies, adding an ErrorAnn if
 * there are inconsistencies.
 *
 * All visit methods to Decl objects return a list of NameTypePair
 * objects indicating the variables and their types.
 */
class DeclChecker
  extends Checker
  implements VarDeclVisitor,
             ConstDeclVisitor,
             InclDeclVisitor
{
  public DeclChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public Object visitVarDecl(VarDecl varDecl)
  {
    //the list of name type pairs in this VarDecl
    List nameTypePairs = list();

    //get and visit the expression
    Expr expr = varDecl.getExpr();
    Type2 exprType = (Type2) expr.accept(exprChecker());

    //expr should be a set expr
    PowerType vPowerType = factory().createPowerType();
    UResult unified = unify(vPowerType, exprType);

    //if the type is not a power type, raise an error
    if (unified == FAIL) {
      ErrorAnn message = errorFactory().nonSetInDecl(expr, exprType);
      error(expr, message);
    }
    //otherwise, create the list of name/type pairs
    else {
      //the type of the variable is the base type of the expr
      Type2 baseType = vPowerType.getType();
      //get the DeclNames
      List<DeclName> declNames = (List<DeclName>) varDecl.getDeclName();
      for (DeclName declName : declNames) {
        //add the name and its type to the list of NameTypePairs
        NameTypePair nameTypePair =
          factory().createNameTypePair(declName, baseType);
        nameTypePairs.add(nameTypePair);
      }
    }

    return nameTypePairs;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    //get the DeclName
    DeclName declName = constDecl.getDeclName();

    debug("visiting ConstDecl " + declName);

    //get and visit the expression
    Expr expr = constDecl.getExpr();
    Type2 exprType = (Type2) expr.accept(exprChecker());

    //create the NameTypePair and the list of decls (only 1 element)
    NameTypePair nameTypePair =
      factory().createNameTypePair(declName, exprType);
    List nameTypePairs = list(nameTypePair);

    return nameTypePairs;
  }

  public Object visitInclDecl(InclDecl inclDecl)
  {
    debug("visiting InclDecl");

    //the list of name type pairs in this InclDecl
    List nameTypePairs = list();

    //get the expression
    Expr expr = inclDecl.getExpr();
    Type2 exprType = (Type2) expr.accept(exprChecker());

    //the included decl must be a schema expr
    SchemaType vSchemaType = factory().createSchemaType();
    PowerType powerType = factory().createPowerType(vSchemaType);
    UResult unified = unify(powerType, exprType);

    //if the decl is not a schema expr, raise an error
    if (unified == FAIL) {
      ErrorAnn message =
        errorFactory().nonSchExprInInclDecl(inclDecl, exprType);
      error(inclDecl, message);
    }
    //otherwise, add the types of the incl decl to the list
    //of name/type pairs
    else {
      LocAnn locAnn = (LocAnn) expr.getAnn(LocAnn.class);
      List<NameTypePair> pairs =
        (List<NameTypePair>) vSchemaType.getSignature().getNameTypePair();
      for (NameTypePair pair : pairs) {
        addAnn(pair.getName(), locAnn);
        nameTypePairs.add(pair);
      }
    }

    return nameTypePairs;
  }
}
