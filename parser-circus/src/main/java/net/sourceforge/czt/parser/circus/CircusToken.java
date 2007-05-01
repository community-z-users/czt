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
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.parser.util.Token;

public enum CircusToken
  implements Token
{
  /* TODO: Maybe include hard-space here "~" for beautification */
  LCIRCCHANSET(CircusString.LCIRCCHANSET),
  RCIRCCHANSET(CircusString.RCIRCCHANSET),
  CIRCLINST(CircusString.CIRCLINST), 
  CIRCRINST(CircusString.CIRCRINST),
  LPAR(CircusString.LPAR), 
  RPAR(CircusString.RPAR), 
  LINTER(CircusString.LINTER), 
  RINTER(CircusString.RINTER), 
  LCIRCGUARD(CircusString.LCIRCGUARD), 
  RCIRCGUARD(CircusString.RCIRCGUARD),
  LSCHEXPRACT(CircusString.LSCHEXPRACT), 
  RSCHEXPRACT(CircusString.RSCHEXPRACT), 
  LCIRCRENAME(CircusString.LCIRCRENAME), 
  RCIRCRENAME(CircusString.RCIRCRENAME),
  
  CIRCUSACTION(CircusString.CIRCUSACTION);

  private String spelling_;

  CircusToken(String spelling)
  {
    spelling_ = spelling;
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
}
