/**
Copyright 2003 Tim Miller
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.parser.oz;

import java_cup.runtime.*;

%%

%class LatexScanner
%public
%unicode
%cupsym LatexSym
%cup
%line
%column

%{
    //records whether the current token is within a class paragraph
    private boolean inOzClass = false;

    //records whether the current token is with a box name
    //i.e. between '{' and '}'
    private boolean inBoxName = false;

    private Symbol symbol(int type) {
      return new Symbol(type, yyline, yycolumn);
    }

    private Symbol symbol(int type, Object value) {
      return new Symbol(type, yyline, yycolumn, value);
    }

    private void log(String msg) {
      System.err.print(msg);
    }

    //Remove a possible extra '}' to close a box name.
    //This is a bit dodgy, but I think is the simplest way to do this.
    private String getBoxName() {
      int bCount = 0; //the number of open brackets
      String result = new String(yytext());

      for (int i = 0; i < yytext().length(); i++) {
        if (yytext().charAt(i) == '{') {
          bCount++;
        }
        else if (yytext().charAt(i) == '}') {
          bCount--;
        }
      }

      //if the name includes the '}' to close the box name
      if (bCount == -1) {
        result = new String(yytext().substring(0, yytext().lastIndexOf('}')));

        //push the '}' character back onto the input stream
        int pushback = yytext().length() -  yytext().lastIndexOf('}');
        yypushback(pushback);
      }
      return result;
    }
%}

LineTerminator  = \r|\n|\r\n
SoftWhiteSpace  = {LineTerminator} | [ \t\f]
HardWhiteSpace  = "~" | "\\," | "\\!" | "\\ " | "\\;" | "\\:" | "\\t"[0-9] |
                  "\\M" | "\\O"

InputCharacter = [^\r\n]
EndOfLineComment     = "%" {InputCharacter}* {LineTerminator}
TraditionalComment   = "/*" [^*] ~"*/"
Comment = {TraditionalComment} | {EndOfLineComment}

//ZCHAR = {DIGIT} | {LETTER} | {SPECIAL} | {SYMBOL}
DIGIT = [0-9]
LETTER = {LATIN} | {GREEK} | {OTHERLETTER}
LATIN = [a-zA-Z]
GREEK = {DELTA} | {XI} | {THETA} | {LAMBDA} | {MU}
OTHERLETTER = {ARITHMOS} | {NAT} | {POWER}
STROKECHAR = {NEXTSTROKE} | {OUTSTROKE} | {INSTROKE}
WORDGLUE = {UP} | {SINGLEUP} | {SINGLEDOWN} | {DOWN} | {ENDGLUE} | {USCORE}

SYMBOL = {CBAR} | {AMPERSAND} | {VDASH} | {LAND} | {LOR} | {IMP} | {IFF} | {LNOT} |
        {FORALL} | {EXISTS} | {CROSS} | {FSLASH} | {EQUALS} | {MEM} | {COLON} |
        {SEMI} | {COMMA} | {PERIOD} | {DOT} |
        {ZHIDE} | {ZPROJECT} | {ZCMP} | {ZPIPE} | {PLUS} |
        {MATHTOOLKITSYMBOL} | {OZTOOLKITSYMBOL}

MATHTOOLKITSYMBOL = 
        "\\rel" | "\\fun" | "\\neq" | "\\notin" | "\\emptyset" |
        "\\subseteq" | "\\subset" | "\\cup" | "\\cap" | "\\setminus" | "\\symdiff" |
        "\\bigcup" | "\\bigcap" | "\\finset" | "\\mapsto" | "\\dom" | "\\ran" |
        "\\id" | "\\comp" | "\\circ" |
        "\\dres" | "\\rres" | "\\ndres" | "\\nrres" | "\\inv" | "\\limg" | "\\rimg" |
        "\\oplus" | "\\plus" | "\\star" | "\\pfun" | "\\pinj" | "\\inj" | "\\psurj" |
        "\\surj" | "\\bij" | "\\ffun" | "\\finj" | "\\disjoint" | "\\partition" |
        "\\num" | "\\negate" | "-" | "*" | "\\div" | "\\mod" |
        "\\leq" | "<" | "\\geq" | ">" | "\\upto" | "\\#" |
        "\\seq" | "\\iseq" | "\\langle" | "\\rangle" | "\\cat" |
        "\\extract" | "\\filter" | "\\prefix" | "\\suffix" | "\\infix" | "\\dcat"

OZTOOLKITSYMBOL = "\\bool" | "\\copyright" | "\\poly" | "\\oid"

//terminals - remember: delta and xi consume any following soft white space
//as part of their name
DELTA = "\\Delta" {SoftWhiteSpace}*
XI = "\\Xi" {SoftWhiteSpace}*
THETA = "\\theta"
MU = "\\mu"
LAMBDA = "\\lambda"

ARITHMOS = "\\arithmos"
NAT = "\\nat"
POWER = "\\power"

NEXTSTROKE = "'"
OUTSTROKE = "!"
INSTROKE = "?"
NUMSTROKE = ( {DOWN} {DIGIT} {ENDGLUE} | {SINGLEDOWN} {DIGIT} )

UP = "^{"
SINGLEUP = "^"
DOWN = "_{"
SINGLEDOWN = "_"
ENDGLUE = "}"

LBRACE = "{"
RBRACE = "}"

USCORE = "\\_"

LPAREN = "("
RPAREN = ")"
LSQBRACE = "["
RSQBRACE = "]" 
LBLOT = "\\lblot"
RBLOT = "\\rblot"
LDATA = "\\ldata"
RDATA = "\\rdata"
LSET = "\\{"
RSET = "\\}"

//Z symbols
CBAR = "|" | "\\cbar"
AMPERSAND = "&"
VDASH = "\\models"
LAND = "\\land"
LOR = "\\lor"
IMP = "\\implies"
IFF = "\\iff"
LNOT = "\\lnot"
FORALL = "\\forall"
EXISTS = "\\exists"
CROSS = "\\cross"
FSLASH = "/"
EQUALS = "="
MEM = "\\in"
COLON = ":"
SEMI = ";"
COMMA = ","
PERIOD = "."
DOT = "@"
ZHIDE = "\\hide"
ZPROJECT = "\\project"
ZCMP = "\\semi"
ZPIPE = "\\pipe"
PLUS = "+"

//other symbols
NL = "\\\\" | "\\also" | "\\znewpage"
SECTION = "\\SECTION"
PARENTS = "\\parents"
TRUE = "true"
FALSE = "false"
LET = "\\LET"
IF = "\\IF"
THEN = "\\THEN"
ELSE = "\\ELSE"
PRECONDITION = "\\pre"
RELATION = "\\relation"
FUNCTION = "\\function"
GENERIC = "\\generic"
LEFTASSOC = "\\leftassoc"
RIGHTASSOC = "\\rightassoc"

LISTARG = "\\listarg"
VARG = "\\varg"

DDEF = "::=" | "\\ddef"
DEFS = "==" | "\\defs"

EXISTS1 = {EXISTS} ( {DOWN} "1" {ENDGLUE} |  {SINGLEDOWN} "1" )

//box characters
END = "\\end" {SoftWhiteSpace}* 
      ( "{axdef}" | "{schema}" | "{gendef}" | "{syntax}" | "{zed}" | 
        "{state}" | "{init}" | "{op}" | "{localdef}" | "{zsection}" )

AX = "\\begin" {SoftWhiteSpace}* "{axdef}"
SCHEMA = "\\begin" {SoftWhiteSpace}* "{schema}"
GENAX = "\\begin" {SoftWhiteSpace}* "{gendef}"
WHERE = "\\where"

//Z paragraphs
//ZED = "\\begin" {SoftWhiteSpace}* "{zed}" | "\\begin" {SoftWhiteSpace}* "{syntax}"
ZED = "\\begin{zed}" | "\\begin{syntax}"

//Z sections
ZSECTION = "\\begin" {SoftWhiteSpace}* "{zsection}"

//object-z box characters
CLASS = "\\begin" {SoftWhiteSpace}* "{class}"
STATE = "\\begin" {SoftWhiteSpace}* "{state}"
INIT = "\\begin" {SoftWhiteSpace}* ( "{init}" | "{schema}" {SoftWhiteSpace}* "{\Init}" )
INITWORD = "\\Init"
OPSCHEMA = "\\begin" {SoftWhiteSpace}* "{op}"
ENDCLASS = "\\end" {SoftWhiteSpace}* "{class}"

//object-z paragraph chars
VISIBILITY = "\\visibility"
INHERITS = "\\inherits"
LOCALDEF = "\\begin" {SoftWhiteSpace}* "{localdef}"

//object-z operation expressions
DCNJ = "\\dcnj"
DGCH = "\\dgch"
DSQC = "\\dsqc"
PARALLEL = "\\parallel"
ASSOCPARALLEL = {PARALLEL} ( ( {DOWN} {OUTSTROKE} {ENDGLUE} ) |
                             ( {SINGLEDOWN} {OUTSTROKE} ) )
GCH = "\\gch"

//Object-Z class comments
CLASSCOM = "\\begin" {SoftWhiteSpace}* "{classcom}"
ENDCLASSCOM = "\\end" {SoftWhiteSpace}* "{classcom}"

NUMBER = {DIGIT}+
STROKE = {STROKECHAR} | {NUMSTROKE}
NAME =  {WORD} {STROKE}*
WORD =  {WORDPART}+ | 
        {LETTER} {ALPHASTR} {WORDPART}* |
        {SYMBOL}+ {WORDPART}*

//This is the original def, but this allows a '}' to end a schema etc name.
//TODO: fix this
WORDPART = {WORDGLUE} ( {ALPHASTR} | {SYMBOL}* )
ALPHASTR = ( {LETTER} | {DIGIT} )*

//The new definition requires it to start with an up or down word glue 
//first, but at the moment does not support nested word glue
//WORDPART = ( 
//             ( {UP} | {DOWN} | {SINGLEUP} | {SINGLEDOWN} ) 
//             ( {ALPHASTR} | {SYMBOL}* ) 
//             ( {ENDGLUE} )
//           )
//ALPHASTR = ( {LETTER} | {DIGIT} | {USCORE} )*

SECTIONNAME = {LATIN} ({LATIN} | {USCORE} | {FSLASH})*

%state ZSECTION OZ CLASSCOMMENT

%%

<YYINITIAL> {

  //Z section
  {ZSECTION}            {
                          yybegin(ZSECTION);
                          log(yytext());
                          return symbol(LatexSym.ZSECTION);
                        }

  //Box characters
  {AX}                  {
                          yybegin(OZ);
                          log(yytext()); 
                          return symbol(LatexSym.AX);
                        }

  {SCHEMA}              { 
                          yybegin(OZ);
                          log(yytext());
                          return symbol(LatexSym.SCHEMA);
                        }

  {GENAX}               {
                          yybegin(OZ);
                          log(yytext());
                          return symbol(LatexSym.GENAX);
                        }

  //Z paragraphs
  {ZED}                 {
                          yybegin(OZ);
                          log(yytext());
                          return symbol(LatexSym.ZED);
                        }

  //Class box
  {CLASS}               {
                          yybegin(OZ);
                          log(yytext());
                          inOzClass = true;
                          return symbol(LatexSym.CLASS);
                        }

  [a-zA-Z]+             {
                          log(yytext());
                          return symbol(LatexSym.NARRWORD, yytext());
                        }


  {Comment}             { /* ignore */ }

  //whitespace
  {HardWhiteSpace}      { log(yytext()); /* ignore */ }        
  {SoftWhiteSpace}      { log(yytext()); /* ignore */ }

}

<OZ> {

  //Greek chars
  {DELTA}               { log(yytext()); return symbol(LatexSym.DELTA); }
  {THETA}               { log(yytext()); return symbol(LatexSym.THETA); }
  {MU}                  { log(yytext()); return symbol(LatexSym.MU); }
  {LAMBDA}              { log(yytext()); return symbol(LatexSym.LAMBDA); }


  {INSTROKE}            { log(yytext()); return symbol(LatexSym.INSTROKE); }
  {OUTSTROKE}           { log(yytext()); return symbol(LatexSym.OUTSTROKE); }
  {NEXTSTROKE}          { log(yytext()); return symbol(LatexSym.NEXTSTROKE); } 
  {NUMSTROKE}           { log(yytext()); return symbol(LatexSym.NUMSTROKE, yytext()); }

  //Brackets etc
  {LPAREN}              { log(yytext()); return symbol(LatexSym.LPAREN); }
  {RPAREN}              { log(yytext()); return symbol(LatexSym.RPAREN); }
  {LSQBRACE}            { log(yytext()); return symbol(LatexSym.LSQBRACE); }
  {RSQBRACE}            { log(yytext()); return symbol(LatexSym.RSQBRACE); }
  {LBLOT}               { log(yytext()); return symbol(LatexSym.LBLOT); }
  {RBLOT}               { log(yytext()); return symbol(LatexSym.RBLOT); }
  {LDATA}               { log(yytext()); return symbol(LatexSym.LDATA); }
  {RDATA}               { log(yytext()); return symbol(LatexSym.RDATA); }
  {LSET}                { log(yytext()); return symbol(LatexSym.LSET); }
  {RSET}                { log(yytext()); return symbol(LatexSym.RSET); }

  //Latex symbols
  {LBRACE}              {
                          log(yytext());
                          inBoxName = true;
                          return symbol(LatexSym.LBRACE);
                        }

  {RBRACE}              { 
                          log(yytext());
                          inBoxName = false;
                          return symbol(LatexSym.RBRACE);
                        }

  //Core symbols
  {CBAR}                { log(yytext()); return symbol(LatexSym.CBAR); }
  {AMPERSAND}           { log(yytext()); return symbol(LatexSym.AMPERSAND); }
  {VDASH}               { log(yytext()); return symbol(LatexSym.VDASH); }
  {LAND}                { log(yytext()); return symbol(LatexSym.LAND); }
  {LOR}                 { log(yytext()); return symbol(LatexSym.LOR); }
  {IMP}                 { log(yytext()); return symbol(LatexSym.IMP); }
  {IFF}                 { log(yytext()); return symbol(LatexSym.IFF); }
  {LNOT}                { log(yytext()); return symbol(LatexSym.LNOT); }
  {FORALL}              { log(yytext()); return symbol(LatexSym.FORALL); }
  {EXISTS}              { log(yytext()); return symbol(LatexSym.EXISTS); }
  {EXISTS1}             { log(yytext()); return symbol(LatexSym.EXISTS1); }
  {CROSS}               { log(yytext()); return symbol(LatexSym.CROSS); }
  {FSLASH}              { log(yytext()); return symbol(LatexSym.FSLASH); }
  {EQUALS}              { log(yytext()); return symbol(LatexSym.EQUALS); }
  {MEM}                 { log(yytext()); return symbol(LatexSym.MEM); }
  {COLON}               { log(yytext()); return symbol(LatexSym.COLON); }
  {SEMI}                { log(yytext()); return symbol(LatexSym.SEMI); }
  {COMMA}               { log(yytext()); return symbol(LatexSym.COMMA); }
  {PERIOD}              { log(yytext()); return symbol(LatexSym.PERIOD); }
  {DOT}                 { log(yytext()); return symbol(LatexSym.DOT); }
  {ZCMP}                { log(yytext()); return symbol(LatexSym.ZCMP); }
  {ZHIDE}               { log(yytext()); return symbol(LatexSym.ZHIDE); }
  {ZPIPE}               { log(yytext()); return symbol(LatexSym.ZPIPE); }

  //Other symbols
  {NL}                  { log(yytext()); return symbol(LatexSym.NL); }
  {TRUE}                { log(yytext()); return symbol(LatexSym.TRUE); }
  {FALSE}               { log(yytext()); return symbol(LatexSym.FALSE); }
  {LET}                 { log(yytext()); return symbol(LatexSym.LET); }
  {IF}                  { log(yytext()); return symbol(LatexSym.IF); }
  {THEN}                { log(yytext()); return symbol(LatexSym.THEN); }
  {ELSE}                { log(yytext()); return symbol(LatexSym.ELSE); }
  {PRECONDITION}        { log(yytext()); return symbol(LatexSym.PRECONDITION); }
  {RELATION}            { log(yytext()); return symbol(LatexSym.RELATION); }
  {FUNCTION}            { log(yytext()); return symbol(LatexSym.FUNCTION); }
  {GENERIC}             { log(yytext()); return symbol(LatexSym.GENERIC); }
  {LEFTASSOC}           { log(yytext()); return symbol(LatexSym.LEFTASSOC); }
  {RIGHTASSOC}          { log(yytext()); return symbol(LatexSym.RIGHTASSOC); }

  {LISTARG}             { log(yytext()); return symbol(LatexSym.LISTARG); }
  {VARG}                { log(yytext()); return symbol(LatexSym.VARG); }

  {DDEF}                { log(yytext()); return symbol(LatexSym.DDEF); }
  {DEFS}                { log(yytext()); return symbol(LatexSym.DEFS); }

  {WHERE}               { log(yytext()); return symbol(LatexSym.WHERE); }

  //Box characters
  {END}                 { if (!inOzClass) {
                              yybegin(YYINITIAL);
                          }
                          log(yytext()); 
                          return symbol(LatexSym.END);
                        }

  {ENDCLASS}            {
                          yybegin(YYINITIAL);
                          log(yytext()); 
                          return symbol(LatexSym.END);
                        }

  {STATE}               { log(yytext()); return symbol(LatexSym.STATE); }
  {INIT}                { log(yytext()); return symbol(LatexSym.INIT); }
  {INITWORD}            { log(yytext()); return symbol(LatexSym.INITWORD); }
  {SCHEMA}              { log(yytext()); return symbol(LatexSym.SCHEMA); }
  {OPSCHEMA}            { log(yytext()); return symbol(LatexSym.OPSCHEMA); }

  //Object-Z paragraph chars
  {VISIBILITY}          { log(yytext()); return symbol(LatexSym.VISIBILITY); }
  {INHERITS}            { log(yytext()); return symbol(LatexSym.INHERITS); }
  {LOCALDEF}            { log(yytext()); return symbol(LatexSym.LOCALDEF); }

  //Object-Z operation expressions
  {DCNJ}                { log(yytext()); return symbol(LatexSym.DCNJ); }
  {DGCH}                { log(yytext()); return symbol(LatexSym.DGCH); }
  {DSQC}                { log(yytext()); return symbol(LatexSym.DSQC); }

  {PARALLEL}            { log(yytext()); return symbol(LatexSym.PARALLEL); }
  {ASSOCPARALLEL}       { log(yytext()); return symbol(LatexSym.ASSOCPARALLEL); }
  {GCH}                 { log(yytext()); return symbol(LatexSym.GCH); }

  //Object-Z class comments
  {CLASSCOM}            {
                          yybegin(CLASSCOMMENT);
                          log(yytext());
                          return symbol(LatexSym.CLASSCOM);
                        }

  //literals
  {NUMBER}              { log(yytext());
                          return symbol(LatexSym.NUMBER, 
                                        new Integer(yytext())); }

  {NAME}                { log(yytext());
                          if (inBoxName) {
                            return symbol(LatexSym.BOXNAME, getBoxName()); 
                          }                         
                          else {
                            return symbol(LatexSym.NAME, yytext()); 
                          }
                        }

  //whitespace
  {HardWhiteSpace}      { /* ignore */ }        
  {SoftWhiteSpace}      { log(yytext()); /* ignore */ }

  {Comment}             { /* ignore */ }
}

<ZSECTION> {

  {SECTION}             { log(yytext()); return symbol(LatexSym.SECTION); }
  {PARENTS}             { log(yytext()); return symbol(LatexSym.PARENTS); }
  {COMMA}               { log(yytext()); return symbol(LatexSym.COMMA); }

  {SECTIONNAME}         { log(yytext());
                          return symbol(LatexSym.NAME, 
                                        new String(yytext())); }
  {END}                 {
                          yybegin(YYINITIAL);
                          log(yytext());
                          return symbol(LatexSym.END);
                        }

  //whitespace
  {HardWhiteSpace}      { log(yytext()); /* ignore */ }        
  {SoftWhiteSpace}      { log(yytext()); /* ignore */ }

  {Comment}             { /* ignore */ }
}

<CLASSCOMMENT> {

  {ENDCLASSCOM}         {
                          yybegin(YYINITIAL);
                          log(yytext());
                          return symbol(LatexSym.ENDCLASSCOM);
                        }

  .                     { log(yytext()); return symbol(LatexSym.CLASSCOMWORD); }

}

//error fallback and narr para
. | \n                  {
                          //if this is a narr para
                          if (yystate() == YYINITIAL) {
                              log(yytext()); 
                              return symbol(LatexSym.NARRWORD, yytext());
                          } else {
                              throw new Error("Illegal character \"" +
                                              yytext() + "\"");
                          }
                        }
