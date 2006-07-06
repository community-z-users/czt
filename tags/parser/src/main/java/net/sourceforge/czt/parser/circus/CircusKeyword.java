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

package net.sourceforge.czt.parser.circus;

import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.circus.util.CircusString;

/**
 * Object-Z keyword spelling for KeywordScanner 
 *
 * @author Leo Freitas
 */
public enum CircusKeyword implements Token {  
  /* Sym elements
  LCIRCCHANSET => 26
  RSCHEXPRACT => 37
  RCIRCCHANSET => 27
  LCIRCGUARD => 34
  RCIRCGUARD => 35
  RCIRCRENAME => 39
  RPAR => 31
  RINTER => 33
  LSCHEXPRACT => 36
  CIRCLINST => 28
  LCIRCRENAME => 38
  CIRCRINST => 29
  LINTER => 32
  CIRCDEF => 25
    */
  /* Circus symbolic keychars*/
  PREFIXCOLON(CircusString.PREFIXCOLON),
  CIRCDEF(CircusString.CIRCDEF),  
  CIRCINDEX(CircusString.CIRCINDEX),
  CIRCMU(CircusString.CIRCMU),
  CIRCTHEN(CircusString.CIRCTHEN),
  CIRCELSE(CircusString.CIRCELSE),
  PREFIXTHEN(CircusString.PREFIXTHEN),
  CIRCASSIGN(CircusString.CIRCASSIGN),
  /**
   * Note: We are reusing ANDALSO instead. See Parser.xml terminal section for an explanation.
   * addKeyword(CircusString.CIRCGUARD, Sym.CIRCGUARD), 
   */
  CIRCSEQ(CircusString.CIRCSEQ),
  /**
   * Note: We are reusing ZCOMP instead. See Parser.xml terminal section for an explanation.
   * addKeyword(CircusString.REPSEQ, Sym.REPSEQ),
   */    
  INTERLEAVE(CircusString.INTERLEAVE),
  REPINTERLEAVE(CircusString.REPINTERLEAVE),   
  REPPARALLEL(CircusString.REPPARALLEL),   
  CIRCHIDING(CircusString.CIRCHIDING),
  EXTCHOICE(CircusString.EXTCHOICE),
  REPEXTCHOICE(CircusString.REPEXTCHOICE),   
  INTCHOICE(CircusString.INTCHOICE),
  REPINTCHOICE(CircusString.REPINTCHOICE),   
  //addKeyword(CircusString.CIRCPARBAR, Sym.CIRCPARBAR),   

  /* Circus language keywords*/
  /**
   * Note: We are reusing ZString.IF instead. See Parser.xml terminal section for an explanation.
   * addKeyword(CircusString.CIRCIF, Sym.CIRCIF),
   */    
  CIRCFI(CircusString.CIRCFI),
  CIRCDO(CircusString.CIRCDO),
  CIRCOD(CircusString.CIRCOD),
  CIRCVAR(CircusString.CIRCVAR),
  CIRCVAL(CircusString.CIRCVAL),
  CIRCRES(CircusString.CIRCRES),
  CIRCVRES(CircusString.CIRCVRES),    
  CIRCSKIP(CircusString.CIRCSKIP),
  CIRCSTOP(CircusString.CIRCSTOP),
  CIRCCHAOS(CircusString.CIRCCHAOS),

  CIRCCHAN(CircusString.CIRCCHAN),
  CIRCCHANFROM(CircusString.CIRCCHANFROM),
  CIRCCHANSET(CircusString.CIRCCHANSET),
  CIRCNAMESET(CircusString.CIRCNAMESET),
  CIRCPROC(CircusString.CIRCPROC),
  CIRCBEGIN(CircusString.CIRCBEGIN),
  CIRCEND(CircusString.CIRCEND),
  CIRCSTATE(CircusString.CIRCSTATE);

  private String spelling_;

  CircusKeyword(String spelling)
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
