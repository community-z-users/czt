/*
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.oz;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;
import net.sourceforge.czt.typecheck.z.*;

/**
 * A <code>PredChecker</code> instance visits the Pred instances in an
 * AST, checks the preds for type consistencies, adding an ErrorAnn if
 * there are inconsistencies.
 *
 * Each visit method returns a <code>UResult</code>, which indicates
 * that the types in the predicate have been partially unified, or
 * not.
 */
public class PredChecker
  extends Checker
{
  //a Z pred checker
  protected net.sourceforge.czt.typecheck.z.PredChecker zPredChecker_;

  public PredChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zPredChecker_ =
      new net.sourceforge.czt.typecheck.z.PredChecker(typeChecker);
  }

  public Object visitTerm(Term term)
  {
    return term.accept(zPredChecker_);
  }
}
