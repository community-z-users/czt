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
    result = updateErrorAnn(result, term);
    //if (result != null) { System.out.println(result.getErrorType() + " = " + result.getErrorMessage()); }
    removeIgnoreAnn(term);
    return result;
  }
}