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

package net.sourceforge.czt.parser.oz;

import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.oz.util.OzString;

/**
 * Object-Z keyword spelling for KeywordScanner 
 *
 * @author Leo Freitas
 */
public enum OzKeyword implements Token {
  DELTA(ZString.DELTA),
  GCH(OzString.GCH),
  PARALLEL(OzString.PARALLEL),
  ASSOPARALLEL(OzString.ASSOPARALLEL),
  DGCH(OzString.DGCH),
  DCNJ(OzString.DCNJ),
  CLASSUNION(OzString.CLASSUNION),
  SDEF(OzString.SDEF),
  POLY(OzString.POLY),
  CONTAINMENT(OzString.CONTAINMENT),
  INITWORD(OzString.INITWORD);

  private String spelling_;

  OzKeyword(String spelling)
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
