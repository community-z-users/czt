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
 * Circus keyword spelling for KeywordScanner 
 *
 * @author Leo Freitas
 */
public enum CircusKeyword implements Token {  
  /* Sym parenthesis-like elements are treated differently.
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
  */
    
  /* Circus language keywords*/
  
  /************************************************** 
   * Keywords with new-lines accepted "before" them *    
   **************************************************/ 
  CIRCOD(CircusString.CIRCOD),              /* \\circod         , od  */
  CIRCEND(CircusString.CIRCEND),            /* \\circend        , end */
  CIRCFI(CircusString.CIRCFI),              /* \\circend        , fi  */
  
  /**
   * Note: 
   * For CIRCIF, we are reusing ZString.IF instead. 
   * See Parser.xml terminal section for an explanation.
   */    
  
  /************************************************** 
   * Keywords with new-lines accepted "after" them  *    
   **************************************************/ 
  CIRCDO(CircusString.CIRCDO),              /* \\circdo         , do          */
  CIRCVAR(CircusString.CIRCVAR),            /* \\circvar        , var         */
  CIRCVAL(CircusString.CIRCVAL),            /* \\circval        , val         */
  CIRCRES(CircusString.CIRCRES),            /* \\circres        , res         */
  CIRCVRES(CircusString.CIRCVRES),          /* \\circvres       , vres        */
  CIRCCHAN(CircusString.CIRCCHAN),          /* \\circchannel    , channel     */
  CIRCCHANFROM(CircusString.CIRCCHANFROM),  /* \\circchannelfrom, channelfrom */
  CIRCCHANSET(CircusString.CIRCCHANSET),    /* \\circchannelset , channelset  */
  CIRCNAMESET(CircusString.CIRCNAMESET),    /* \\circnameset    , nameset     */
  CIRCPROC(CircusString.CIRCPROC),          /* \\circprocess    , process     */
  CIRCBEGIN(CircusString.CIRCBEGIN),        /* \\circbegin      , begin       */
  CIRCSTATE(CircusString.CIRCSTATE),        /* \\circstate      , state       */
  REPINTERLEAVE(CircusString.REPINTERLEAVE),/* \\Interleave     , U+2AFC      */   
  REPPARALLEL(CircusString.REPPARALLEL),    /* \\Parallel       , U+2225      */ 
  REPEXTCHOICE(CircusString.REPEXTCHOICE),  /* \\Extchoice      , U+25A1      */   
  REPINTCHOICE(CircusString.REPINTCHOICE),  /* \\Intchoice      , U+2294      */

  /************************************************** 
   * Keywords with new-lines accepted both b/a them *    
   **************************************************/ 
  CIRCDEF(CircusString.CIRCDEF),            /* \\circdef        , U+2259 */            
  CIRCINDEX(CircusString.CIRCINDEX),        /* \\circindex      , U+2299 */            
  CIRCTHEN(CircusString.CIRCTHEN),          /* \\circthen       , U+27FC */
  CIRCELSE(CircusString.CIRCELSE),          /* \\circelse       , U+25AF */
  PREFIXTHEN(CircusString.PREFIXTHEN),      /* \\then           , U+27F6 */
  PREFIXCOLON(CircusString.PREFIXCOLON),    /* \\prefixcolon    , U+2236 */
  CIRCSEQ(CircusString.CIRCSEQ),            /* \\circseq        , U+037E */
  INTERLEAVE(CircusString.INTERLEAVE),      /* \\interleave     , U+2980 */
  CIRCHIDING(CircusString.CIRCHIDING),      /* \\circhide       , U+2AF5 */
  EXTCHOICE(CircusString.EXTCHOICE),        /* \\extchoice      , U+25FB */
  INTCHOICE(CircusString.INTCHOICE),        /* \\intchoice      , U+2293 */
  CIRCASSIGN(CircusString.CIRCASSIGN),      /* :=               , :=     */
  CIRCREFINES(CircusString.CIRCREFINES),    /* \\circrefines    , U+2291 */
  CIRCMU(CircusString.CIRCMU),              /* \\circmu         , U+00B5 */
  
  /**
   * Note: 
   * For REPSEQ we are reusing ZCOMP instead. 
   * For CIRCGUARD we are reusing ANDALSO instead. 
   * See Parser.xml terminal section for an explanation.   
   *
   * QUESTION: Should CIRCASSIGN be given a LaTeX command? 
   */                                                  
  
  /************************************************** 
   * Keywords without new-lines accepted (no-fix)   *    
   **************************************************/   
  CIRCSKIP(CircusString.CIRCSKIP),
  CIRCSTOP(CircusString.CIRCSTOP),
  CIRCCHAOS(CircusString.CIRCCHAOS);

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
