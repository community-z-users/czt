/*
  Copyright (C) 2006 Leo Freitas
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation); either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY); without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt); if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.circus;

import net.sourceforge.czt.circus.util.CircusString;
import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;

/**
 * These tokens are for the ContextFreeScanner that occurs before
 * decorwords are translated into keywords, so that the context
 * sensitive lexing can take place. TODO: review this list and
 * add CIRCUS box into here (which may solve the \begin{circus} 
 * problem with \begin{zed} within the scanners.
 */
public enum CircusToken  
  implements Token
{
  /* TODO: Maybe include hard-space here "~" for beautification */
  LCIRCCHANSET(CircusString.LCIRCCHANSET, NewlineCategory.AFTER),
  RCIRCCHANSET(CircusString.RCIRCCHANSET, NewlineCategory.BEFORE),
  CIRCLINST(CircusString.CIRCLINST, NewlineCategory.AFTER),
  CIRCRINST(CircusString.CIRCRINST, NewlineCategory.BEFORE),
  LPAR(CircusString.LPAR, NewlineCategory.BOTH),
  RPAR(CircusString.RPAR, NewlineCategory.BOTH),
  LINTER(CircusString.LINTER, NewlineCategory.BOTH),
  RINTER(CircusString.RINTER, NewlineCategory.BOTH),
  LCIRCGUARD(CircusString.LCIRCGUARD, NewlineCategory.AFTER),
  RCIRCGUARD(CircusString.RCIRCGUARD, NewlineCategory.BEFORE),
  LSCHEXPRACT(CircusString.LSCHEXPRACT, NewlineCategory.AFTER),
  RSCHEXPRACT(CircusString.RSCHEXPRACT, NewlineCategory.BEFORE),
  LCIRCRENAME(CircusString.LCIRCRENAME, NewlineCategory.AFTER),
  RCIRCRENAME(CircusString.RCIRCRENAME, NewlineCategory.BEFORE),

  CIRCUS(CircusString.CIRCUS, NewlineCategory.BOTH),
  CIRCUSACTION(CircusString.CIRCUSACTION, NewlineCategory.BOTH);

  private String spelling_;
  private NewlineCategory newlineCategory_;

  CircusToken(String spelling, NewlineCategory newlineCategory)
  {
    spelling_ = spelling;
    newlineCategory_ = newlineCategory;
  }

  public String getName()
  {
    return toString();
  }

  public Object getSpelling()
  {
    return spelling_;
  }

  public String spelling()
  {
    return spelling_;
  }

  public NewlineCategory getNewlineCategory()
  {
    return newlineCategory_;
  }
}
