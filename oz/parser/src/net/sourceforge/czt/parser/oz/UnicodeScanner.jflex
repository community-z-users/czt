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
package net.sourceforge.czt.parser.oz;

import java.io.*;

import java_cup.runtime.*;

import net.sourceforge.czt.scanner.CztReader;
      
%%
   
/* -----------------Options and Declarations Section----------------- */
   
%class UnicodeScanner
%unicode
%line
%column
%char
%cupsym LatexSym
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

      UnicodeScanner lexer = new UnicodeScanner(reader);
      OutputStreamWriter writer = new OutputStreamWriter(System.out);
      lexer.setWriter(writer);
      Symbol s = null;
      while ( (s = lexer.next_token()).sym != LatexSym.EOF) {
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
      writer_.write("LINE(" + getLine() + ")COL(" + getColumn() + ")");
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
  {ZED}         {  yybegin(Z); log("BOX(ZED)"); return symbol(LatexSym.ZED); }
  {AX}          {  yybegin(Z); log("BOX(AX)"); return symbol(LatexSym.AX); }
  {GENAX}       {  yybegin(Z); log("BOX(GENAX)"); return symbol(LatexSym.GENAX); }
  {SCH}         {  yybegin(Z); log("BOX(SCH)"); return symbol(LatexSym.SCH); }
  {GENSCH}      {  yybegin(Z); log("BOX(GENSCH)"); return symbol(LatexSym.GENSCH); }
  [^]           {  return symbol(LatexSym.TEXT, yytext()); }
}

<Z> {
  /* Keywords (7.4.2 and 7.4.3) */
  "else"        { log("keyword(else)"); return symbol(LatexSym.ELSE); }
  "false"       { log("keyword(false)"); return symbol(LatexSym.FALSE); }
  "function"    { log("keyword(function)"); return symbol(LatexSym.FUNCTION); }
  "generic"     { log("keyword(generic)"); return symbol(LatexSym.GENERIC); }
  "if"          { log("keyword(if)"); return symbol(LatexSym.IF); }
  "leftassoc"   { log("keyword(leftassoc)"); return symbol(LatexSym.LEFTASSOC); }
  "let"         { log("keyword(let)"); return symbol(LatexSym.LET); }
  "\u2119"      { log("keyword(power)"); return symbol(LatexSym.POWER); }
  "parents"     { log("keyword(parents)"); return symbol(LatexSym.PARENTS); }
  "pre"         { log("keyword(pre)"); return symbol(LatexSym.ZPRE); }
  "relation"    { log("keyword(relation)"); return symbol(LatexSym.RELATION); }
  "rightassoc"  { log("keyword(rightassoc)"); return symbol(LatexSym.RIGHTASSOC); }
  "section"     { log("keyword(section)"); return symbol(LatexSym.SECTION); }
  "then"        { log("keyword(then)"); return symbol(LatexSym.THEN); }
  "true"        { log("keyword(true)"); return symbol(LatexSym.TRUE); }
  ":"           { log("keyword(:)"); return symbol(LatexSym.COLON); }
  "=="          { log("keyword(==)"); return symbol(LatexSym.DEFEQUAL); }
  ","           { log("keyword(,)"); return symbol(LatexSym.COMMA); }
  "::="         { log("keyword(::=)"); return symbol(LatexSym.DEFFREE); }
  "|"           { log("keyword(|)"); return symbol(LatexSym.BAR); }
  "&"           { log("keyword(&)"); return symbol(LatexSym.ANDALSO); }
  "\u2055"      { log("keyword(zhide)"); return symbol(LatexSym.ZHIDE); }
  "/"           { log("keyword(/)"); return symbol(LatexSym.SLASH); }
  "."           { log("keyword(.)"); return symbol(LatexSym.DOT); }
  ";"           { log("keyword(;)"); return symbol(LatexSym.SEMICOLON); }
  "\u005F"      { log("keyword(arg)"); return symbol(LatexSym.ARG); }
  ",,"          { log("keyword(,,)"); return symbol(LatexSym.LISTARG); }
  "="           { log("keyword(equals)"); return symbol(LatexSym.EQUALS); }
  "\u22A2?"     { log("keyword(conjecture)"); return symbol(LatexSym.CONJECTURE); }
  "\u2200"      { log("keyword(all)"); return symbol(LatexSym.ALL); }
  "\u2981"      { log("keyword(spot)"); return symbol(LatexSym.SPOT); }
  "\u2203"      { log("keyword(exi)"); return symbol(LatexSym.EXI); }
  "\u2203\u21981\u2196" { log("keyword(exione)"); return symbol(LatexSym.EXIONE); }
  "\u21D4"      { log("keyword(iff)"); return symbol(LatexSym.IFF); }
  "\u21D2"      { log("keyword(imp)"); return symbol(LatexSym.IMP); }
  "\u2228"      { log("keyword(or)"); return symbol(LatexSym.OR); }
  "\u2227"      { log("keyword(and)"); return symbol(LatexSym.AND); }
  "\u00AC"      { log("keyword(not)"); return symbol(LatexSym.NOT); }
  "\u2208"      { log("keyword(mem)"); return symbol(LatexSym.MEM); }
  "\u2A21"      { log("keyword(zproj)"); return symbol(LatexSym.ZPROJ); }
  "\u00D7"      { log("keyword(cross)"); return symbol(LatexSym.CROSS); }
  "\u03BB"      { log("keyword(lambda)"); return symbol(LatexSym.LAMBDA); }
  "\u03BC"      { log("keyword(mu)"); return symbol(LatexSym.MU); }
  "\u03B8"      { log("keyword(theta)"); return symbol(LatexSym.THETA); }
  "\u2A1F"      { log("keyword(zcomp)"); return symbol(LatexSym.ZCOMP); }
  "\u2A20"      { log("keyword(zpipe)"); return symbol(LatexSym.ZPIPE); }

  /* Boxes */
  {END}         {  yybegin(YYINITIAL);
                   log("BOX(END)\n"); return symbol(LatexSym.END); }
  {NL}          {  log("BOX(NL)\n"); return symbol(LatexSym.NL); }

  /* strip spaces (context-sensitive lexis; 7.4.1)
     \t is added so that unicode files containing tabs
     can be read properly */
  {SPACE} | {CONTROL} {  log(" "); }

  /* Brackets */
  {LPAREN}      {  log("PAREN(LPAREN)"); return symbol(LatexSym.LPAREN); }
  {RPAREN}      {  log("PAREN(RPAREN)"); return symbol(LatexSym.RPAREN); }
  {LSQUARE}     {  log("PAREN(LSQUARE)"); return symbol(LatexSym.LSQUARE); }
  {RSQUARE}     {  log("PAREN(RSQUARE)"); return symbol(LatexSym.RSQUARE); }
  {LBRACE}      {  log("PAREN(LBRACE)"); return symbol(LatexSym.LBRACE); }
  {RBRACE}      {  log("PAREN(RBRACE)"); return symbol(LatexSym.RBRACE); }
  {LBIND}       {  log("PAREN(LBIND)"); return symbol(LatexSym.LBIND); }
  {RBIND}       {  log("PAREN(RBIND)"); return symbol(LatexSym.RBIND); }
  {LDATA}       {  log("PAREN(LDATA)"); return symbol(LatexSym.LDATA); }
  {RDATA}       {  log("PAREN(RDATA)"); return symbol(LatexSym.RDATA); }
  {INSTROKE}    {  log("STROKE(IN)"); return symbol(LatexSym.INSTROKE); }
  {OUTSTROKE}   {  log("STROKE(OUT)"); return symbol(LatexSym.OUTSTROKE); }
  {NEXTSTROKE}  {  log("STROKE(NEXT)"); return symbol(LatexSym.NEXTSTROKE); }
  {SE} {DIGIT} {NW}
                {  Integer digit = new Integer(yytext().substring(1,2));
                   log("STROKE(" + digit + ")");
                   return symbol(LatexSym.NUMSTROKE, digit);
                }
  {NUMERAL}     {  log("NUMERAL(" + yytext() + ")");
                   return symbol(LatexSym.NUMERAL, new Integer(yytext())); }
  {DECORWORD}   {  log("DECORWORD(" + yytext() + ")");
                   return symbol(LatexSym.DECORWORD, yytext()); }

  /* error fallback */
  .             {
                   String message = "Unexpected character <" + yytext() + ">";
                   throw new Error(getLine() + ", " + getColumn() + ":" + message);
                }
}
