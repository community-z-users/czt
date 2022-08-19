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

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;

/**
 * A <code>DeclChecker</code> instance visits the Decl instances in an
 * AST, checks the preds for type consistencies, adding an ErrorAnn if
 * there are inconsistencies.
 *
 * All visit methods to Decl objects return a list of NameTypePair
 * objects indicating the variables and their types.
 */
public class DeclChecker
  extends Checker<List<NameTypePair>>
  implements VarDeclVisitor<List<NameTypePair>>,
             ConstDeclVisitor<List<NameTypePair>>,
             InclDeclVisitor<List<NameTypePair>>,
             ZDeclListVisitor<List<NameTypePair>>
{
  public DeclChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public List<NameTypePair> visitVarDecl(VarDecl varDecl)
  {
    //get and visit the expression
    Expr expr = varDecl.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    //expr should be a set expr
    PowerType vPowerType = factory().createPowerType();
    UResult unified = unify(vPowerType, exprType);

    //the list of name type pairs in this VarDecl
    List<NameTypePair> pairs = checkVarDecl(varDecl, unified,
                                            exprType, vPowerType);   
    
    return pairs;
  }

  public List<NameTypePair> visitConstDecl(ConstDecl constDecl)
  {
    //get the Name
    ZName constName = constDecl.getZName();

    //get and visit the expression
    Expr expr = constDecl.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    //add a unique ID to this name
    factory().addNameID(constName);

    //create the NameTypePair and the list of decls (only 1 element)
    NameTypePair pair = factory().createNameTypePair(constName, exprType);
    List<NameTypePair> pairs = factory().list(pair);

    return pairs;
  }

  public List<NameTypePair> visitInclDecl(InclDecl inclDecl)
  {
    //the list of name type pairs in this InclDecl
    List<NameTypePair> pairs = factory().list();

    //get the expression
    Expr expr = inclDecl.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    //the included decl must be a schema expr
    SchemaType vSchemaType = factory().createSchemaType();
    PowerType powerType = factory().createPowerType(vSchemaType);
    UResult unified = unify(powerType, exprType);

    //if the decl is not a schema expr, raise an error
    if (unified == FAIL) {
      Object [] params = {inclDecl, exprType};
      error(inclDecl, ErrorMessage.NON_SCHEXPR_IN_INCLDECL, params);
    }
    //otherwise, add the types of the incl decl to the list
    //of name/type pairs
    else {
      LocAnn locAnn = (LocAnn) expr.getAnn(LocAnn.class);
      List<NameTypePair> lPairs = vSchemaType.getSignature().getNameTypePair();
      for (NameTypePair pair : lPairs) {
        //copy the name
        ZName newName = factory().createZName(pair.getZName(), true);
	addAnn(newName, locAnn);

        NameTypePair newPair =
          factory().createNameTypePair(newName, pair.getType());
        pairs.add(newPair);
      }
    }

    return pairs;
  }

  public List<NameTypePair> visitZDeclList(ZDeclList zDeclList)
  {
    List<NameTypePair> pairs = factory().list();

    //for each declaration in the list, get the declarations from that
    for (Decl decl : zDeclList.getDecl()) {
      List<NameTypePair> nextPairs = decl.accept(declChecker());
      pairs.addAll(nextPairs);
    }
    return pairs;
  }
}
