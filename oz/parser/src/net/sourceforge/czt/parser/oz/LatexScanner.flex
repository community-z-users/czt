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

    private Symbol symbol(int type) {
        return new Symbol(type, yyline, yycolumn);
    }

    private Symbol symbol(int type, Object value) {
        return new Symbol(type, yyline, yycolumn, value);
    }

    private void log(String msg) {
        System.err.print(msg + " ");
    }
%}

LineTerminator  = \r|\n|\r\n
SoftWhiteSpace  = {LineTerminator} | [ \t\f]
HardWhiteSpace  = "~" | "\\," | "\\!" | "\\ " | "\\;" | "\\:" | "\t"[0-9] |
                  "\\M" | "\\O"

InputCharacter = [^\r\n]
EndOfLineComment     = "//" {InputCharacter}* {LineTerminator}
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
        "\\bigcup" | "\\bigcap" | "\\finset" | "\\mapsto" | "\\comp" | "\\circ" |
        "\\dres" | "\\rres" | "\\ndres" | "\\nrres" | "\\inv" | "\\limg" | "\\rimg" |
        "\\oplus" | "\\plus" | "\\star" | "\\pfun" | "\\pinj" | "\\inj" | "\\psurj" |
        "\\surj" | "\\bij" | "\\ffun" | "\\finj" |
        "\\num" | "\\negate" | "-" | "*" | "\\div" | "\\mod" |
        "\\leq" | "<" | "\\geq" | ">" | "\\upto" | "\\#" |
        "\\langle" | "\\rangle" | "\\cat" | "\\extract" | "\\filter" | "\\dcat"

OZTOOLKITSYMBOL = "\\bool" | "\\copyright" | "\\poly" | "\\oid"

//terminals - remember: greek characters consume any following soft white space
DELTA = "\\Delta"
XI = "\\Xi"
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
NL = "\\\\" | "\\also"
SECTION = "\\zsection"
PARENTS = "parents"
TRUE = "true"
FALSE = "false"
LET = "let"
IF = "\\IF"
THEN = "\\THEN"
ELSE = "\\ELSE"
PRECONDITION = "\\pre"
RELATION = "relation"
FUNCTION = "function"
GENERIC = "generic"
LEFTASSOC = "leftassoc"
RIGHTASSOC = "rightassoc"
LISTARG = ",,"

DDEF = "::=" | "\\ddef"
DEFS = "==" | "\\defs"

EXISTS1 = {EXISTS} ( {DOWN} "1" {ENDGLUE} |  {SINGLEDOWN} "1" )

//box characters
END = "\\end{axdef}" | "\\end{schema}" | "\\end{gendef}" | "\\end{syntax}" |
      "\\end{zed}" | "\\end{class}" | "\\end{state}" | "\\end{init}" |
      "\\end{op}" | "\\end{localdef}"

AX = "\\begin{axdef}"
SCHEMA = "\\begin{schema}"
GENAX = "\\begin{gendef}"
WHERE = "\\where"

//Z paragraphs
ZED = "\\begin{zed}" | "\\begin{syntax}"

//object-z box characters
CLASS = "\\begin{class}"
STATE = "\\begin{state}"
INIT = "\\begin{init}" | "\\begin{schema}{\Init}"
INITWORD = "\Init"
OPSCHEMA = "\\begin{op}"

//object-z paragraph chars
VISIBILITY = "\\visibility"
INHERITS = "\\inherits"
LOCALDEF = "\\begin{localdef}"

//object-z operation expressions
DCNJ = "\\dcnj"
DGCH = "\\dgch"
DSQC = "\\dsqc"
PARALLEL = "\\parallel"
ASSOCPARALLEL = {PARALLEL} ( ( {DOWN} {OUTSTROKE} {ENDGLUE} ) |
                             ( {SINGLEDOWN} {OUTSTROKE} ) )
GCH = "\\gch"

//Object-Z class comments
CLASSCOM = "\\begin{classcom}"
ENDCLASSCOM = "\\end{classcom}"

NUMBER = {DIGIT}+
STROKE = {STROKECHAR} | {NUMSTROKE}
NAME =  {WORD} {STROKE}*
WORD =  {WORDPART}+ | 
        {LETTER} {ALPHASTR} {WORDPART}* |
        {SYMBOL}+ {WORDPART}*

//This is the original def, but this allows a '}' to end a schema etc name.
//WORDPART = {WORDGLUE} ( {ALPHASTR} | {SYMBOL}* )

//The new definition requires it to start with an up or down word glue 
//first, but at the moment does not support nested word glue
WORDPART = ( 
             ( {UP} | {DOWN} | {SINGLEUP} | {SINGLEDOWN} ) 
             ( {ALPHASTR} | {SYMBOL}* ) 
             ( {ENDGLUE} )
           )
ALPHASTR = ( {LETTER} | {DIGIT} | {USCORE} )*

SECTIONNAME = {LATIN} ({LATIN} | {USCORE} | {FSLASH})*

%state ZSECTION OZ CLASSCOMMENT

%%

<YYINITIAL> {

  //Z section
  {SECTION}             {
                          yybegin(ZSECTION);
                          log(yytext());
                          return symbol(LatexSym.SECTION);
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

  {Comment}             { /* ignore */ }

  //whitespace
  {HardWhiteSpace}      { /* ignore */ }        
  {SoftWhiteSpace}      { /* ignore */ }

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
  {LBRACE}              { log(yytext()); return symbol(LatexSym.LBRACE); }
  {RBRACE}              { log(yytext()); return symbol(LatexSym.RBRACE); }
  {USCORE}              { log(yytext()); return symbol(LatexSym.USCORE); }


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
                          return symbol(LatexSym.NAME, 
                                        new String(yytext())); }

  //whitespace
  {HardWhiteSpace}      { /* ignore */ }        
  {SoftWhiteSpace}      { /* ignore */ }

  {Comment}             { /* ignore */ }
}


<ZSECTION> {

  {PARENTS}             { log(yytext()); return symbol(LatexSym.PARENTS); }
  {COMMA}               { log(yytext()); return symbol(LatexSym.COMMA); }

  {SECTIONNAME}         { log(yytext());
                          return symbol(LatexSym.NAME, 
                                        new String(yytext())); }
  {NL}                  {
                          yybegin(YYINITIAL);
                          log(yytext());
                          return symbol(LatexSym.NL);
                        }

  //whitespace
  {HardWhiteSpace}      { /* ignore */ }        
  {SoftWhiteSpace}      { /* ignore */ }

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
.|\n                    {
                          //if this is a narr para
                          if (yystate() == YYINITIAL) {
                              log(yytext()); 
                              return symbol(LatexSym.NARRWORD, yytext());
                          } else {
                              throw new Error("Illegal character \"" +
                                              yytext() + "\"");
                          }
                        }
