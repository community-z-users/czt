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

package net.sourceforge.czt.parser.tcoz;

import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.tcoz.util.TcozString;

/**
 * Timed Object-Z keyword spelling for KeywordScanner 
 *
 * @author Leo Freitas
 */
public enum TcozKeyword implements Token {
  ATTIME(TcozString.ATTIME),
  NEXTPRO(TcozString.NEXTPRO),
  INTCHOICE(TcozString.INTCHOICE),
  DIC(TcozString.DIC),
  INTERLEAVE(TcozString.INTERLEAVE),
  DIL(TcozString.DIL),
  WAITUNTIL("waituntil"),
  DEADLINE("deadline"),
  WAIT("wait"),
  INTERRUPT(TcozString.INTERRUPT),
  TIMEOUT(TcozString.TIMEOUT),
  TIMEEND(TcozString.TIMEEND),
  DPARA(TcozString.DPARA),
  NETTOPLEFT(TcozString.NETTOPLEFT),
  NETTOPRIGHT(TcozString.NETTOPRIGHT),
  CHAN("chan"),
  SENSOR("sensor"),
  ACTUATOR("actuator");

  private String spelling_;

  TcozKeyword(String spelling)
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
