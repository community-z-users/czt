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
package net.sourceforge.czt.scanner;

import java.io.*;
import java_cup.runtime.*;
      
%%
   
/* -----------------Options and Declarations Section----------------- */
   
%class UnicodeLexer
%unicode
%line
%column
%char
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

      UnicodeLexer lexer = new UnicodeLexer(reader);
      OutputStreamWriter writer = new OutputStreamWriter(System.out);
      lexer.setWriter(writer);
      Symbol s = null;
      while ( (s = lexer.next_token()).sym != sym.EOF) {
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
    return new Symbol(type, yyline, yycolumn);
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
    return new Symbol(type, yyline, yycolumn, value);
  }

  public void setWriter(Writer writer)
  {
    writer_ = writer;
  }

  private void log(String message)
    throws IOException
  {
    if (writer_ != null) {
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

%state Z

%%
/* ------------------------Lexical Rules Section---------------------- */

<YYINITIAL> {
  {ZED}         {  yybegin(Z); log("BOX(ZED)"); return symbol(sym.ZED); }
  {AX}          {  yybegin(Z); log("BOX(AX)"); return symbol(sym.AX); }
  {GENAX}       {  yybegin(Z); log("BOX(GENAX)"); return symbol(sym.GENAX); }
  {SCH}         {  yybegin(Z); log("BOX(SCH)"); return symbol(sym.SCH); }
  {GENSCH}      {  yybegin(Z); log("BOX(GENSCH)"); return symbol(sym.GENSCH); }
  [^]           {  return symbol(sym.TEXT, yytext()); }
}

<Z> {
  /* Keywords (7.4.2 and 7.4.3) */
  "else"        { log("keyword(else)"); return symbol(sym.ELSE); }
  "false"       { log("keyword(false)"); return symbol(sym.FALSE); }
  "function"    { log("keyword(function)"); return symbol(sym.FUNCTION); }
  "generic"     { log("keyword(generic)"); return symbol(sym.GENERIC); }
  "if"          { log("keyword(if)"); return symbol(sym.IF); }
  "leftassoc"   { log("keyword(leftassoc)"); return symbol(sym.LEFTASSOC); }
  "let"         { log("keyword(let)"); return symbol(sym.LET); }
  "\u2119"      { log("keyword(power)"); return symbol(sym.POWER); }
  "parents"     { log("keyword(parents)"); return symbol(sym.PARENTS); }
  "pre"         { log("keyword(pre)"); return symbol(sym.ZPRE); }
  "relation"    { log("keyword(relation)"); return symbol(sym.RELATION); }
  "rightassoc"  { log("keyword(rightassoc)"); return symbol(sym.RIGHTASSOC); }
  "section"     { log("keyword(section)"); return symbol(sym.SECTION); }
  "then"        { log("keyword(then)"); return symbol(sym.THEN); }
  "true"        { log("keyword(true)"); return symbol(sym.TRUE); }
  ":"           { log("keyword(:)"); return symbol(sym.COLON); }
  "=="          { log("keyword(==)"); return symbol(sym.DEFEQUAL); }
  ","           { log("keyword(,)"); return symbol(sym.COMMA); }
  "::="         { log("keyword(::=)"); return symbol(sym.DEFFREE); }
  "|"           { log("keyword(|)"); return symbol(sym.BAR); }
  "&"           { log("keyword(&)"); return symbol(sym.ANDALSO); }
  "\u2055"      { log("keyword(zhide)"); return symbol(sym.ZHIDE); }
  "/"           { log("keyword(/)"); return symbol(sym.SLASH); }
  "."           { log("keyword(.)"); return symbol(sym.DOT); }
  ";"           { log("keyword(;)"); return symbol(sym.SEMICOLON); }
  "\u005F"      { log("keyword(arg)"); return symbol(sym.ARG); }
  ",,"          { log("keyword(,,)"); return symbol(sym.LISTARG); }
  "="           { log("keyword(equals)"); return symbol(sym.EQUALS); }
  "\u22A2?"     { log("keyword(conjecture)"); return symbol(sym.CONJECTURE); }
  "\u2200"      { log("keyword(all)"); return symbol(sym.ALL); }
  "\u2981"      { log("keyword(spot)"); return symbol(sym.SPOT); }
  "\u2203"      { log("keyword(exi)"); return symbol(sym.EXI); }
  "\u2203\u21981\u2196" { log("keyword(exione)"); return symbol(sym.EXIONE); }
  "\u21D4"      { log("keyword(iff)"); return symbol(sym.IFF); }
  "\u21D2"      { log("keyword(imp)"); return symbol(sym.IMP); }
  "\u2228"      { log("keyword(or)"); return symbol(sym.OR); }
  "\u2227"      { log("keyword(and)"); return symbol(sym.AND); }
  "\u00AC"      { log("keyword(not)"); return symbol(sym.NOT); }
  "\u2208"      { log("keyword(mem)"); return symbol(sym.MEM); }
  "\u2A21"      { log("keyword(zproj)"); return symbol(sym.ZPROJ); }
  "\u00D7"      { log("keyword(cross)"); return symbol(sym.CROSS); }
  "\u03BB"      { log("keyword(lambda)"); return symbol(sym.LAMBDA); }
  "\u03BC"      { log("keyword(mu)"); return symbol(sym.MU); }
  "\u03B8"      { log("keyword(theta)"); return symbol(sym.THETA); }
  "\u2A1F"      { log("keyword(zcomp)"); return symbol(sym.ZCOMP); }
  "\u2A20"      { log("keyword(zpipe)"); return symbol(sym.ZPIPE); }

  /* Boxes */
  {END}         {  yybegin(YYINITIAL);
                   log("BOX(END)\n"); return symbol(sym.END); }
  {NL}          {  log("BOX(NL)\n"); return symbol(sym.NL); }

  /* strip spaces (context-sensitive lexis; 7.4.1)
     \t is added so that unicode files containing tabs
     can be read properly */
  {SPACE} | {CONTROL} {  log(" "); }

  /* Brackets */
  {LPAREN}      {  log("PAREN(LPAREN)"); return symbol(sym.LPAREN); }
  {RPAREN}      {  log("PAREN(RPAREN)"); return symbol(sym.RPAREN); }
  {LSQUARE}     {  log("PAREN(LSQUARE)"); return symbol(sym.LSQUARE); }
  {RSQUARE}     {  log("PAREN(RSQUARE)"); return symbol(sym.RSQUARE); }
  {LBRACE}      {  log("PAREN(LBRACE)"); return symbol(sym.LBRACE); }
  {RBRACE}      {  log("PAREN(RBRACE)"); return symbol(sym.RBRACE); }
  {LBIND}       {  log("PAREN(LBIND)"); return symbol(sym.LBIND); }
  {RBIND}       {  log("PAREN(RBIND)"); return symbol(sym.RBIND); }
  {LDATA}       {  log("PAREN(LDATA)"); return symbol(sym.LDATA); }
  {RDATA}       {  log("PAREN(RDATA)"); return symbol(sym.RDATA); }

  {STROKE}      {  log("STROKE(" + yytext() + ")");
                   return symbol(sym.STROKE, yytext()); }
  {NUMERAL}     {  log("NUMERAL(" + yytext() + ")");
                   return symbol(sym.NUMERAL, new Integer(yytext())); }
  {DECORWORD}   {  log("DECORWORD(" + yytext() + ")");
                   return symbol(sym.DECORWORD, yytext()); }

  /* error fallback */
  .             {
                   String message = "Unexpected character <" + yytext() + ">";
                   throw new ScanException(message, yyline, yycolumn);
                }
}
