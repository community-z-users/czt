package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.Iterator;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.util.impl.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * At the end of the typechecker, this checker visits any previously
 * unresolved SetExprs and RefExprs (expressions that may introduce a
 * variable type into their type) to ensure that all implicit
 * parameters have been determined
 */
class PostChecker
  extends Checker
  implements RefExprVisitor,
             SetExprVisitor
{
  //the position of the current error/term
  protected int position_;

  public PostChecker(CheckerInfo info)
  {
    super(info);
    position_ = 0;
  }

  public void postCheck()
  {
    for (position_ = 0; position_ < errors().size(); position_++) {
      Object next = errors().get(position_);
      if (next instanceof Expr) {
        Expr expr = (Expr) next;
        expr.accept(this);
      }
    }
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    //get the ParameterAnn and check that no types in the list are
    //still unresolved
    ParameterAnn pAnn = (ParameterAnn) refExpr.getAnn(ParameterAnn.class);

    if (pAnn != null) {
      List params = pAnn.getParameters();
      for (Iterator iter = params.iterator(); iter.hasNext(); ) {
        Type2 type = (Type2) iter.next();
        //if the type is not resolved, then replace the expr with an
        //error annotation
        if (resolve(type) instanceof VariableType) {
          ErrorAnn message =
            errorFactory().parametersNotDetermined(refExpr);
          errors().set(position_, message);
          refExpr.getAnns().add(message);
          return null;
        }
      }
    }
    else {
      throw new CztException("No ParameterAnn object in RefExpr");
    }

    //if there is no error, remove this from the list
    //decrementing position to allow for the removed item
    errors().remove(position_--);
    return null;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    //get the type from the annotations
    Type2 type = getTypeFromAnns(setExpr);

    if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      Type2 innerType = powerType.getType();

      //if the inner type is not resolved, then replace the expr with an
      //error annotation
      if (resolve(innerType) instanceof VariableType) {
        ErrorAnn message = errorFactory().parametersNotDetermined(setExpr);
        errors().set(position_, message);
        setExpr.getAnns().add(message);
        return null;
      }
    }

    //if there is no error, remove this from the list
    //decrementing position to allow for the removed item
    errors().remove(position_--);
    return null;
  }
}
