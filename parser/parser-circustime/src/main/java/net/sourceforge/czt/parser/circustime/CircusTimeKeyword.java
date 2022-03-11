
/*
  Copyright (C) 2006 Leo Freitas
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation), either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY), without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt), if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.circustime;

import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.circustime.util.CircusTimeString;

/**
 * Circus keyword spelling for KeywordScanner 
 *
 * These are the keywords for the context senstitive lexis (see Z standard
 * and the context sensitive lexer, as the keyword scanner). Context 
 * sensitive lexing happens after the context free scanner transforms
 * DecorWord strings into Keywords. TODO: Rearrange this and CircusToken,
 * trying to follow a logical arrangement of keywords and tokens like 
 * what was done in the Z standard.
 *
 * @author Leo Freitas
 */
public enum CircusTimeKeyword implements Token {  
  /* Support for Circus Time */
  CIRCWAIT(CircusTimeString.CIRCWAIT, NewlineCategory.AFTER),
  CIRCENDBY(CircusTimeString.CIRCENDBY, NewlineCategory.BOTH),
  CIRCSTARTBY(CircusTimeString.CIRCSTARTBY, NewlineCategory.BOTH),
  CIRCTIMEOUT(CircusTimeString.CIRCTIMEOUT, NewlineCategory.BOTH),
  CIRCTIMEDINTERRUPT(CircusTimeString.CIRCTIMEDINTERRUPT, NewlineCategory.BOTH),
  ATTIME(CircusTimeString.ATTIME, NewlineCategory.BOTH); 

 
  private String spelling_;
  private NewlineCategory newlineCategory_;

  CircusTimeKeyword(String spelling, NewlineCategory newlineCategory)
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
