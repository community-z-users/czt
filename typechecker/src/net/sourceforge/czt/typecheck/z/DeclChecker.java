package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.Iterator;

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
      List declNames = varDecl.getDeclName();
      for (Iterator iter = declNames.iterator(); iter.hasNext(); ) {
        DeclName declName = (DeclName) iter.next();

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
    //the list of name type pairs in this ConstDecl
    //(this list will have only one element)
    List nameTypePairs = list();

    //get the DeclName
    DeclName declName = constDecl.getDeclName();

    debug("visiting ConstDecl " + declName);

    //get and visit the expression
    Expr expr = constDecl.getExpr();
    Type2 exprType = (Type2) expr.accept(exprChecker());

    //create the NameTypePair and add it to the list
    NameTypePair nameTypePair =
      factory().createNameTypePair(declName, exprType);
    nameTypePairs.add(nameTypePair);

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
      List declPairs = vSchemaType.getSignature().getNameTypePair();
      nameTypePairs.addAll(declPairs);
    }

    return nameTypePairs;
  }
}
