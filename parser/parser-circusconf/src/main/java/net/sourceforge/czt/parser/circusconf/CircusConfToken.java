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

package net.sourceforge.czt.parser.circusconf;

import net.sourceforge.czt.circusconf.util.CircusConfString;
import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;

/**
 * These tokens are for the ContextFreeScanner that occurs before
 * decorwords are translated into keywords, so that the context
 * sensitive lexing can take place. TODO: review this list and
 * add CIRCUS box into here (which may solve the \begin{circus} 
 * problem with \begin{zed} within the scanners.
 */
public enum CircusConfToken  
  implements Token
{

  /* Support for Circus Time */
  LCIRCCONF(CircusConfString.LCIRCCONF, NewlineCategory.AFTER),
  RCIRCCONF(CircusConfString.RCIRCCONF, NewlineCategory.BEFORE);

  private String spelling_;
  private NewlineCategory newlineCategory_;

  CircusConfToken(String spelling, NewlineCategory newlineCategory)
  {
    spelling_ = spelling;
    newlineCategory_ = newlineCategory;
  }

  @Override
public String getName()
  {
    return toString();
  }

  @Override
public Object getSpelling()
  {
    return spelling_;
  }

  @Override
public String spelling()
  {
    return spelling_;
  }

  @Override
public NewlineCategory getNewlineCategory()
  {
    return newlineCategory_;
  }
}
