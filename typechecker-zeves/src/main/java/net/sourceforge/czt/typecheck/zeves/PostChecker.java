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

package net.sourceforge.czt.typecheck.zeves;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ErrorType;

/**
 *
 * @author Leo Freitas
 * @date Aug 17, 2011
 */
public class PostChecker
  extends Checker<net.sourceforge.czt.typecheck.z.ErrorAnn>
{

  //a Z expr checker
  protected net.sourceforge.czt.typecheck.z.PostChecker zPostChecker_;

  public PostChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zPostChecker_ = new net.sourceforge.czt.typecheck.z.PostChecker(typeChecker);
  }

  @Override
  public net.sourceforge.czt.typecheck.z.ErrorAnn visitTerm(Term term)
  {
    // post check
    net.sourceforge.czt.typecheck.z.ErrorAnn result = term.accept(zPostChecker_);

    // if there is a result that is about undeclared identifiers, and the term given
    // was tagged as one to ignore undeclared names with, then mark it as a warning.
    if (result != null && term.getAnn(Checker.IngnoreUndeclNameAnn.class) != null &&
            (result.getErrorMessage().equals(net.sourceforge.czt.typecheck.z.ErrorMessage.UNDECLARED_IDENTIFIER.toString()) ||
             result.getErrorMessage().equals(net.sourceforge.czt.typecheck.z.ErrorMessage.UNDECLARED_IDENTIFIER_IN_EXPR.toString())))
    {
//      warningManager().warn(term, WarningMessage.UNDECLARED_NAME_ERROR_AS_WARNING, term.getClass().getName() + " = " + result.toString());
//      result = null;//result.setErrorType(ErrorType.WARNING);
      result = errorAnn(term, ErrorMessage.UNDECLARED_NAME_ERROR_AS_WARNING, new Object[] { term.getClass().getName(), result.toString() });
      result.setErrorType(ErrorType.WARNING);
    }
    return result;
  }
}