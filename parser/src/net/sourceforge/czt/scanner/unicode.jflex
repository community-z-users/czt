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

import java_cup.runtime.*;
      
%%
   
/* -----------------Options and Declarations Section----------------- */
   
%class UnicodeLexer
%unicode
%line
%column
%cup
   
%{   
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
NEXTSTROKE = "\u02B9" /* modifier letter prime */

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
LDATA = "\u300A"   /* left double angle bracket */
RDATA = "\u300B"   /* right double angle bracket */

/* Box characters (6.4.4.3) */
BOXCHAR = {ZEDCHAR} | {AXCHAR} | {SCHCHAR} | {GENCHAR} | {ENDCHAR}
ZEDCHAR = "\u2028" /* line separator */
AXCHAR = "\u2577"  /* box drawings light down */
SCHCHAR = "\u250C" /* box drawings light down and right */
GENCHAR = "\u2550" /* box drawings double horizontal */
ENDCHAR = "\u2029" /* paragraph separator */

/* Other SPECIAL characters (6.4.4.5) */
NLCHAR = "\u000A"
SPACE =   "\u0020"


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

%%
/* ------------------------Lexical Rules Section---------------------- */

<YYINITIAL> {
  /* Keywords (7.4.2 and 7.4.3) */
  "else"        { return symbol(sym.ELSE); }
  "false"       { return symbol(sym.FALSE); }
  "function"    { return symbol(sym.FUNCTION); }
  "generic"     { return symbol(sym.GENERIC); }
  "if"          { return symbol(sym.IF); }
  "leftassoc"   { return symbol(sym.LEFTASSOC); }
  "let"         { return symbol(sym.LET); }
  "\u2119"      { return symbol(sym.POWER); }
  "parents"     { return symbol(sym.PARENTS); }
  "pre"         { return symbol(sym.ZPRE); }
  "relation"    { return symbol(sym.RELATION); }
  "rightassoc"  { return symbol(sym.RIGHTASSOC); }
  "section"     { return symbol(sym.SECTION); }
  "then"        { return symbol(sym.THEN); }
  "true"        { return symbol(sym.TRUE); }
  ":"           { return symbol(sym.COLON); }
  "=="          { return symbol(sym.DEFEQUAL); }
  ","           { return symbol(sym.COMMA); }
  "::="         { return symbol(sym.DEFFREE); }
  "|"           { return symbol(sym.BAR); }
  "&"           { return symbol(sym.ANDALSO); }
  "\u2055"      { return symbol(sym.ZHIDE); }
  "/"           { return symbol(sym.SLASH); }
  "."           { return symbol(sym.DOT); }
  ";"           { return symbol(sym.SEMICOLON); }
  "\u005F"      { return symbol(sym.ARG); }
  ",,"          { return symbol(sym.LISTARG); }
  "="           { return symbol(sym.EQUALS); }
  "\u22A2?"     { return symbol(sym.CONJECTURE); }
  "\u2200"      { return symbol(sym.ALL); }
  "\u2981"      { return symbol(sym.SPOT); }
  "\u2203"      { return symbol(sym.EXI); }
  "\u2203\u21981\u2196" { return symbol(sym.EXIONE); }
  "\u21D4"      { return symbol(sym.IFF); }
  "\u21D2"      { return symbol(sym.IMP); }
  "\u2228"      { return symbol(sym.OR); }
  "\u2227"      { return symbol(sym.AND); }
  "\u00AC"      { return symbol(sym.NOT); }
  "\u2208"      { return symbol(sym.MEM); }
  "\u2A21"      { return symbol(sym.ZPROJ); }
  "\u00D7"      { return symbol(sym.CROSS); }
  "\u03BB"      { return symbol(sym.LAMBDA); }
  "\u03BC"      { return symbol(sym.MU); }
  "\u03B8"      { return symbol(sym.THETA); }
  "\u2A1F"      { return symbol(sym.ZCOMP); }
  "\u2A20"      { return symbol(sym.ZPIPE); }

  /* Boxes */
  {ZED}         {  return symbol(sym.ZED); }
  {AX}          {  return symbol(sym.AX); }
  {GENAX}       {  return symbol(sym.GENAX); }
  {SCH}         {  return symbol(sym.SCH); }
  {GENSCH}      {  return symbol(sym.GENSCH); }
  {END}         {  return symbol(sym.END); }
  {NL}          {  return symbol(sym.NL); }
  {SPACE}| "\t" {  /* strip spaces (context-sensitive lexis; 7.4.1)
                      \t is added so that unicode files containing tabs
                      can be read properly */}

  /* Brackets */
  {LPAREN}      {  return symbol(sym.LPAREN); }
  {RPAREN}      {  return symbol(sym.RPAREN); }
  {LSQUARE}     {  return symbol(sym.LSQUARE); }
  {RSQUARE}     {  return symbol(sym.RSQUARE); }
  {LBRACE}      {  return symbol(sym.LBRACE); }
  {RBRACE}      {  return symbol(sym.RBRACE); }
  {LBIND}       {  return symbol(sym.LBIND); }
  {RBIND}       {  return symbol(sym.RBIND); }
  {LDATA}       {  return symbol(sym.LDATA); }
  {RDATA}       {  return symbol(sym.RDATA); }

  {STROKE}      {  return symbol(sym.STROKE, yytext()); }
  {NUMERAL}     {  return symbol(sym.NUMERAL, new Integer(yytext())); }
  {DECORWORD}   {  return symbol(sym.DECORWORD, yytext()); }

  /* error fallback */
  .|\n          { throw new Error("Illegal character <" + yytext() + ">"); }
}
