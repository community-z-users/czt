/**
Copyright 2003 Petra Malik
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

++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

This is the jflex description of a lexer for lexing Z specifications
in unicode format as described in the Z standard (Working Draft 2.7;
October 12, 2001).  Numbers in brackets contained in comments refer to
the corresponding sections in this document.
*/

/* --------------------------Usercode Section------------------------ */
package @PACKAGE@;

import java.io.*;
import java_cup.runtime.*;

import net.sourceforge.czt.scanner.CztReader;
import net.sourceforge.czt.scanner.ScanException;
%%
   
/* -----------------Options and Declarations Section----------------- */
   
%class @CLASS@
%unicode
%line
%column
%char
%cupsym @SYM@
%cup

%{
  /**
   * A writer for writing logging messages.
   */
  private Writer writer_;

  /**
   * Lexes a given file.
   */
  public static void main(String argv[]) {    
    try {
      InputStream stream = new FileInputStream(argv[0]);
      InputStreamReader reader = new InputStreamReader(stream, "UTF-8");

      @CLASS@ lexer = new @CLASS@(reader);
      OutputStreamWriter writer = new OutputStreamWriter(System.out);
      lexer.setWriter(writer);
      Symbol s = null;
      while ( (s = lexer.next_token()).sym != @SYM@.EOF) {
      }
      writer.close();
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

  /**
   * Creates a new java_cup.runtime.Symbol with line and column
   * information about the current token.
   * The token will have no value.
   */
  private Symbol symbol(int type)
  {
    return new Symbol(type, getLine(), getColumn());
  }

  /**
   * Creates a new java_cup.runtime.Symbol with line and column
   * information about the current token.
   *
   * @param value the value of the Symbol to be returned.
   * @return a new Symbol with column and line information
   *         and the given value.
   */
  private Symbol symbol(int type, Object value)
  {
    return new Symbol(type, getLine(), getColumn(), value);
  }

  public void setWriter(Writer writer)
  {
    writer_ = writer;
  }

  private int getLine()
  {
    if (yy_reader instanceof CztReader) {
      CztReader reader = (CztReader) yy_reader;
      return reader.getLine(yychar);
    }
    return yyline;
  }

  private int getColumn()
  {
    if (yy_reader instanceof CztReader) {
      CztReader reader = (CztReader) yy_reader;
      return reader.getColumn(yychar);
    }
    return yycolumn;
  }

  private void log(String message)
    throws IOException
  {
    if (writer_ != null) {
      //      writer_.write("LINE(" + getLine() + ")COL(" + getColumn() + ")");
      writer_.write(message);
    }
  }
%}
   
/***********************************************************************
  Z characters (6.2)
 ***********************************************************************/

/* TODO: Distinguish between DIGIT and DECIMAL */
DIGIT = {DECIMAL}
DECIMAL = [:digit:]

/* TODO: What about OTHERLETTER? */
LETTER = [:letter:]

SPECIAL =   {STROKECHAR}
          | {WORDGLUE}
          | {BRACKET}
          | {BOXCHAR}
          | {NLCHAR}
          | {SPACE}
          | {CONTROL}

/* NOT_SYMBOL ist only needed to define SYMBOL */
NOT_SYMBOL = {DIGIT} | {LETTER} | {SPECIAL} | "\t"

/* SYMBOL are all the characters that are not NOT_SYMBOL */
SYMBOL = !(![^] | {NOT_SYMBOL})

/* SPECIAL
   ======= */

/* Stroke */
STROKECHAR = {INSTROKE} | {OUTSTROKE} | {NEXTSTROKE}
INSTROKE = "\u003F"   /* question mark */
OUTSTROKE = "\u0021"  /* exclamation mark */
NEXTSTROKE = "\u2032" | "'" /* prime */

/* Word glue (6.4.4.2) */
WORDGLUE = {NE} | {SE} | {SW} | {NW} | {LL}
NE = "\u2197" /* north east arrow */
SW = "\u2199" /* south west arrow */
SE = "\u2198" /* south east arrow */
NW = "\u2196" /* north west arrow */
LL = "\u005F" /* low line */

/* Bracket characters (6.4.4.3) */
BRACKET = {LPAREN} | {RPAREN} | {LSQUARE} | {RSQUARE} | {LBRACE} | {RBRACE} | {LBIND} | {RBIND} | {LDATA} | {RDATA}
LPAREN = "\u0028"  /* left parenthesis */
RPAREN = "\u0029"  /* right parenthesis */
LSQUARE = "\u005B" /* left square bracket */
RSQUARE = "\u005D" /* right square bracket */
LBRACE = "\u007B"  /* left curly bracket */
RBRACE = "\u007D"  /* right curly bracket */
LBIND = "\u2989"   /* Z notation left binding bracket */
RBIND = "\u298A"   /* Z notation right binding bracket */
LDATA = "\u27EA"   /* mathmatical left double angle bracket */
RDATA = "\u27EB"   /* mathmatical right double angle bracket */

/* Box characters (6.4.4.3) */
BOXCHAR = {ZEDCHAR} | {AXCHAR} | {SCHCHAR} | {GENCHAR} | {ENDCHAR}
ZEDCHAR = "\u2500" /* box drawings light horizontal */
AXCHAR = "\u2577"  /* box drawings light down */
SCHCHAR = "\u250C" /* box drawings light down and right */
GENCHAR = "\u2550" /* box drawings double horizontal */
ENDCHAR = "\u2029" /* paragraph separator */

/* Other SPECIAL characters (6.4.4.5) */
NLCHAR = "\u2028" | {CR} {LF} | {CR} | {LF}  /* line separator TODO add BEF*/
SPACE =   "\u0020" /* space */

CONTROL = {TAB}
LF = "\n"
CR = "\r"
TAB = "\t"

/***********************************************************************
  Lexis (7)
 ***********************************************************************/

DECORWORD = {WORD} {STROKE}*
WORD =   {WORDPART}+
       | {LETTER} {ALPHASTR} {WORDPART}*
       | {SYMBOL}+ {WORDPART}*
WORDPART = {WORDGLUE} ( {ALPHASTR} | {SYMBOL}* )
ALPHASTR = ({LETTER} | {DIGIT})*
NUMERAL = {DIGIT}+
STROKE = {STROKECHAR} | {SE} {DIGIT} {NW}
ZED = {ZEDCHAR}
AX = {AXCHAR}
SCH = {SCHCHAR}
GENAX = {AXCHAR} {GENCHAR}
GENSCH = {SCHCHAR} {GENCHAR}
END = {ENDCHAR}
NL = {NLCHAR}

NOT_BOXCHAR = !(![^] | {BOXCHAR})
TEXT = {NOT_BOXCHAR}*

%state Z

%%
/* ------------------------Lexical Rules Section---------------------- */

<YYINITIAL> {
  {ZED}         {  yybegin(Z); log("BOX(ZED)"); return symbol(@SYM@.ZED); }
  {AX}          {  yybegin(Z); log("BOX(AX)"); return symbol(@SYM@.AX); }
  {GENAX}       {  yybegin(Z); log("BOX(GENAX)"); return symbol(@SYM@.GENAX); }
  {SCH}         {  yybegin(Z); log("BOX(SCH)"); return symbol(@SYM@.SCH); }
  {GENSCH}      {  yybegin(Z); log("BOX(GENSCH)"); return symbol(@SYM@.GENSCH); }
  {TEXT}        {  return symbol(@SYM@.TEXT, yytext()); }
}

<Z> {
  /* Keywords (7.4.2 and 7.4.3) */
  "else"        { log("keyword(else)"); return symbol(@SYM@.ELSE); }
  "false"       { log("keyword(false)"); return symbol(@SYM@.FALSE); }
  "function"    { log("keyword(function)"); return symbol(@SYM@.FUNCTION); }
  "generic"     { log("keyword(generic)"); return symbol(@SYM@.GENERIC); }
  "if"          { log("keyword(if)"); return symbol(@SYM@.IF); }
  "leftassoc"   { log("keyword(leftassoc)"); return symbol(@SYM@.LEFTASSOC); }
  "let"         { log("keyword(let)"); return symbol(@SYM@.LET); }
  "\u2119"      { log("keyword(power)"); return symbol(@SYM@.POWER); }
  "parents"     { log("keyword(parents)"); return symbol(@SYM@.PARENTS); }
  "pre"         { log("keyword(pre)"); return symbol(@SYM@.ZPRE); }
  "relation"    { log("keyword(relation)"); return symbol(@SYM@.RELATION); }
  "rightassoc"  { log("keyword(rightassoc)"); return symbol(@SYM@.RIGHTASSOC); }
  "section"     { log("keyword(section)"); return symbol(@SYM@.SECTION); }
  "then"        { log("keyword(then)"); return symbol(@SYM@.THEN); }
  "true"        { log("keyword(true)"); return symbol(@SYM@.TRUE); }
  ":"           { log("keyword(:)"); return symbol(@SYM@.COLON); }
  "=="          { log("keyword(==)"); return symbol(@SYM@.DEFEQUAL); }
  ","           { log("keyword(,)"); return symbol(@SYM@.COMMA); }
  "::="         { log("keyword(::=)"); return symbol(@SYM@.DEFFREE); }
  "|"           { log("keyword(|)"); return symbol(@SYM@.BAR); }
  "&"           { log("keyword(&)"); return symbol(@SYM@.ANDALSO); }
  "\u2055"      { log("keyword(zhide)"); return symbol(@SYM@.ZHIDE); }
  "/"           { log("keyword(/)"); return symbol(@SYM@.SLASH); }
  "."           { log("keyword(.)"); return symbol(@SYM@.DOT); }
  ";"           { log("keyword(;)"); return symbol(@SYM@.SEMICOLON); }
  "\u005F"      { log("keyword(arg)"); return symbol(@SYM@.ARG); }
  ",,"          { log("keyword(,,)"); return symbol(@SYM@.LISTARG); }
  "="           { log("keyword(equals)"); return symbol(@SYM@.EQUALS); }
  "\u22A2?"     { log("keyword(conjecture)"); return symbol(@SYM@.CONJECTURE); }
  "\u2200"      { log("keyword(all)"); return symbol(@SYM@.ALL); }
  "\u2981"      { log("keyword(spot)"); return symbol(@SYM@.SPOT); }
  "\u2203"      { log("keyword(exi)"); return symbol(@SYM@.EXI); }
  "\u2203\u21981\u2196" { log("keyword(exione)"); return symbol(@SYM@.EXIONE); }
  "\u21D4"      { log("keyword(iff)"); return symbol(@SYM@.IFF); }
  "\u21D2"      { log("keyword(imp)"); return symbol(@SYM@.IMP); }
  "\u2228"      { log("keyword(or)"); return symbol(@SYM@.OR); }
  "\u2227"      { log("keyword(and)"); return symbol(@SYM@.AND); }
  "\u00AC"      { log("keyword(not)"); return symbol(@SYM@.NOT); }
  "\u2208"      { log("keyword(mem)"); return symbol(@SYM@.MEM); }
  "\u2A21"      { log("keyword(zproj)"); return symbol(@SYM@.ZPROJ); }
  "\u00D7"      { log("keyword(cross)"); return symbol(@SYM@.CROSS); }
  "\u03BB"      { log("keyword(lambda)"); return symbol(@SYM@.LAMBDA); }
  "\u03BC"      { log("keyword(mu)"); return symbol(@SYM@.MU); }
  "\u03B8"      { log("keyword(theta)"); return symbol(@SYM@.THETA); }
  "\u2A1F"      { log("keyword(zcomp)"); return symbol(@SYM@.ZCOMP); }
  "\u2A20"      { log("keyword(zpipe)"); return symbol(@SYM@.ZPIPE); }

  /* Boxes */
  {END}         {  yybegin(YYINITIAL);
                   log("BOX(END)\n"); return symbol(@SYM@.END); }
  {NL}          {  log("BOX(NL)\n"); return symbol(@SYM@.NL); }

  /* strip spaces (context-sensitive lexis; 7.4.1)
     \t is added so that unicode files containing tabs
     can be read properly */
  {SPACE} | {CONTROL} {  log(" "); }

  /* Brackets */
  {LPAREN}      {  log("PAREN(LPAREN)"); return symbol(@SYM@.LPAREN); }
  {RPAREN}      {  log("PAREN(RPAREN)"); return symbol(@SYM@.RPAREN); }
  {LSQUARE}     {  log("PAREN(LSQUARE)"); return symbol(@SYM@.LSQUARE); }
  {RSQUARE}     {  log("PAREN(RSQUARE)"); return symbol(@SYM@.RSQUARE); }
  {LBRACE}      {  log("PAREN(LBRACE)"); return symbol(@SYM@.LBRACE); }
  {RBRACE}      {  log("PAREN(RBRACE)"); return symbol(@SYM@.RBRACE); }
  {LBIND}       {  log("PAREN(LBIND)"); return symbol(@SYM@.LBIND); }
  {RBIND}       {  log("PAREN(RBIND)"); return symbol(@SYM@.RBIND); }
  {LDATA}       {  log("PAREN(LDATA)"); return symbol(@SYM@.LDATA); }
  {RDATA}       {  log("PAREN(RDATA)"); return symbol(@SYM@.RDATA); }
  {INSTROKE}    {  log("STROKE(IN)"); return symbol(@SYM@.INSTROKE); }
  {OUTSTROKE}   {  log("STROKE(OUT)"); return symbol(@SYM@.OUTSTROKE); }
  {NEXTSTROKE}  {  log("STROKE(NEXT)"); return symbol(@SYM@.NEXTSTROKE); }
  {SE} {DIGIT} {NW}
                {  Integer digit = new Integer(yytext().substring(1,2));
                   log("STROKE(" + digit + ")");
                   return symbol(@SYM@.NUMSTROKE, digit);
                }
  {NUMERAL}     {  log("NUMERAL(" + yytext() + ")");
                   return symbol(@SYM@.NUMERAL, new Integer(yytext())); }
  {DECORWORD}   {  log("DECORWORD(" + yytext() + ")");
                   return symbol(@SYM@.DECORWORD, yytext()); }

  /* error fallback */
  .             {
                   String message = "Unexpected character <" + yytext() + ">";
                   throw new ScanException(message, getLine(), getColumn());
                }
}
