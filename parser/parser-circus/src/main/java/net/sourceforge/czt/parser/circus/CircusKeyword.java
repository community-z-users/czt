
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

import net.sourceforge.czt.parser.util.NewlineCategory;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.circus.util.CircusString;

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
  CIRCOD(CircusString.CIRCOD, NewlineCategory.BEFORE),      /* \\circod         , od  */
  CIRCEND(CircusString.CIRCEND, NewlineCategory.BEFORE),    /* \\circend        , end */
  CIRCFI(CircusString.CIRCFI, NewlineCategory.BEFORE),      /* \\circend        , fi  */
  
  /**
   * Note: 
   * For CIRCIF, we are reusing ZString.IF instead. 
   * See Parser.xml terminal section for an explanation.
   */    
  
  /************************************************** 
   * Keywords with new-lines accepted "after" them  *    
   **************************************************/ 
  CIRCDO(CircusString.CIRCDO, NewlineCategory.AFTER),       /* \\circdo         , do          */
  CIRCVAR(CircusString.CIRCVAR, NewlineCategory.AFTER),     /* \\circvar        , var         */
  CIRCVAL(CircusString.CIRCVAL, NewlineCategory.AFTER),            /* \\circval        , val         */
  CIRCRES(CircusString.CIRCRES, NewlineCategory.AFTER),            /* \\circres        , res         */
  CIRCVRES(CircusString.CIRCVRES, NewlineCategory.AFTER),          /* \\circvres       , vres        */
  CIRCCHAN(CircusString.CIRCCHAN, NewlineCategory.AFTER),          /* \\circchannel    , channel     */
  CIRCCHANFROM(CircusString.CIRCCHANFROM, NewlineCategory.AFTER),  /* \\circchannelfrom, channelfrom */
  CIRCCHANSET(CircusString.CIRCCHANSET, NewlineCategory.AFTER),    /* \\circchannelset , channelset  */
  CIRCNAMESET(CircusString.CIRCNAMESET, NewlineCategory.AFTER),    /* \\circnameset    , nameset     */
  CIRCPROC(CircusString.CIRCPROC, NewlineCategory.AFTER),          /* \\circprocess    , process     */
  CIRCASSERTREF(CircusString.CIRCASSERTREF, NewlineCategory.AFTER),/* \\circassertref  , assert      */
  CIRCBEGIN(CircusString.CIRCBEGIN, NewlineCategory.AFTER),        /* \\circbegin      , begin       */
  CIRCSTATE(CircusString.CIRCSTATE, NewlineCategory.AFTER),        /* \\circstate      , circstate   */
  REPINTERLEAVE(CircusString.REPINTERLEAVE, NewlineCategory.AFTER),/* \\Interleave     , U+2AFC      */   
  REPPARALLEL(CircusString.REPPARALLEL, NewlineCategory.AFTER),    /* \\Parallel       , U+2225      */ 
  REPEXTCHOICE(CircusString.REPEXTCHOICE, NewlineCategory.AFTER),  /* \\Extchoice      , U+25A1      */   
  REPINTCHOICE(CircusString.REPINTCHOICE, NewlineCategory.AFTER),  /* \\Intchoice      , U+2294      */

  /************************************************** 
   * Keywords with new-lines accepted both b/a them *    
   **************************************************/ 
  CIRCDEF(CircusString.CIRCDEF, NewlineCategory.BOTH),            /* \\circdef        , U+2259 */            
  CIRCINDEX(CircusString.CIRCINDEX, NewlineCategory.BOTH),        /* \\circindex      , U+2299 */            
  CIRCSPOT(CircusString.CIRCSPOT, NewlineCategory.BOTH),          /* \\circspot       , U+2219 */            
  CIRCTHEN(CircusString.CIRCTHEN, NewlineCategory.BOTH),          /* \\circthen       , U+27FC */
  CIRCELSE(CircusString.CIRCELSE, NewlineCategory.BOTH),          /* \\circelse       , U+25AF */
  PREFIXTHEN(CircusString.PREFIXTHEN, NewlineCategory.BOTH),      /* \\then           , U+27F6 */
  PREFIXCOLON(CircusString.PREFIXCOLON, NewlineCategory.BOTH),    /* \\prefixcolon    , U+2236 */
  CIRCSEQ(CircusString.CIRCSEQ, NewlineCategory.BOTH),            /* \\circseq        , U+037E */
  INTERLEAVE(CircusString.INTERLEAVE, NewlineCategory.BOTH),      /* \\interleave     , U+2980 */
  CIRCHIDING(CircusString.CIRCHIDING, NewlineCategory.BOTH),      /* \\circhide       , U+2AF5 */
  CIRCINTERRUPT(CircusString.CIRCINTERRUPT, NewlineCategory.BOTH),/* \\circinterrupt  , U+25C2?*/
  EXTCHOICE(CircusString.EXTCHOICE, NewlineCategory.BOTH),        /* \\extchoice      , U+25FB */
  INTCHOICE(CircusString.INTCHOICE, NewlineCategory.BOTH),        /* \\intchoice      , U+2293 */
  CIRCASSIGN(CircusString.CIRCASSIGN, NewlineCategory.BOTH),      /* :=               , :=     */
  CIRCREFINES(CircusString.CIRCREFINES, NewlineCategory.BOTH),    /* \\circrefines    , U+2291 */
  CIRCSIMULATES(CircusString.CIRCSIMULATES, NewlineCategory.BOTH),/* \\circsimulates  , U+227C */
  CIRCMU(CircusString.CIRCMU, NewlineCategory.AFTER),              /* \\circmu         , U+00B5 */
  
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
  CIRCSKIP(CircusString.CIRCSKIP, NewlineCategory.NEITHER),
  CIRCSTOP(CircusString.CIRCSTOP, NewlineCategory.NEITHER),
  CIRCCHAOS(CircusString.CIRCCHAOS, NewlineCategory.NEITHER);

  private String spelling_;
  private NewlineCategory newlineCategory_;

  CircusKeyword(String spelling, NewlineCategory newlineCategory)
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
