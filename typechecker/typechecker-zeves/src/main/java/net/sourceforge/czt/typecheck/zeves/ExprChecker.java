/*
Copyright (C) 2007 Leo Freitas
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
package net.sourceforge.czt.typecheck.zeves;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.visitor.RenameExprVisitor;
import net.sourceforge.czt.zeves.ast.InstantiationList;

/**
 * Visitor that checks Circus expressions. They are channel set display expressions,
 * and sigma expressions, which represent channel selection like "c.1" or "c.true".
 *
 * @author Leo Freitas
 */
public class ExprChecker
  extends Checker<Type2>
  implements RenameExprVisitor<Type2>
{  

  //a Z expr checker
  protected net.sourceforge.czt.typecheck.z.ExprChecker zExprChecker_;

  public ExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zExprChecker_ = new net.sourceforge.czt.typecheck.z.ExprChecker(typeChecker);    
  }
  
  @Override
  public Type2 visitTerm(Term term)
  {
    checkIfNeedIgnoreUndeclNameTag(term);
    //checkIfNeedBindTag(term);
    return term.accept(zExprChecker_);
  }

  @Override
  public Type2 visitRenameExpr(RenameExpr term)
  {
    if (term.getRenameList() instanceof InstantiationList)
    {
        Type2 type = factory().createUnknownType();

        //visit the expr
        Expr expr = term.getExpr();
        Type2 exprType = expr.accept(exprChecker());

        SchemaType vSchemaType = factory().createSchemaType();
        PowerType vPowerType = factory().createPowerType(vSchemaType);
        UResult unified = unify(vPowerType, exprType);

        //if the expr is not a schema type, raise an error
        if (unified == UResult.FAIL) {
          Object [] params = {term, exprType};
          error(term, net.sourceforge.czt.typecheck.z.ErrorMessage.NON_SCHEXPR_IN_RENAMEEXPR, params);
        }
        //if the expr is a schema reference, perform the renaming
        else {
          //raise a warning for now: let Z/EVES do it.
          getTypeChecker().getWarningManager().warn(term,
                  WarningMessage.IGNORE_ZEVES_THMREPLACEMENT_TYPECHECK,
                  term.getExpr());
        }

        //add the type annotation
        addTypeAnn(term, type);

        return type;
    }
    else
      return term.accept(zExprChecker_);
  }
}
