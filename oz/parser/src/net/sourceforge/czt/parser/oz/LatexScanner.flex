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
    /** Stroke characters */
    public final static char SHRIEK = '!';
    public final static char QST_MARK = '?';
    public final static char PRIME = '\'';
    public final static char STROKE_USCORE = '_';

    /** Super and subscript characters */
    public final static char UPTOK = '^';
    public final static char STARTGLUE = '{';
    public final static char ENDGLUE = '}';

    /** Word glue */
    public final static String UPGLUE = "^{";
    public final static String DOWNGLUE = "_{";
    public final static String USCORE = "\\_";

    //records whether the current token is within a class paragraph.
    //This is because an object-z class is a special type of paragraph,
    //in that it can contain other paragraphs
    private boolean inOzClass = false;

    //records whether the current token is within a box name
    //i.e. between '{' and '}'
    private boolean inBoxName = false;

    //records whether the current token is within a word glue word
    private boolean inWordGlue = false;

    //print the debug info?
    private boolean debug_ = true;

    /**
     * Changes the debug mode
     */
    public void setDebug(boolean debug)
    {
      debug_ = debug;
    }

    private Symbol symbol(int type) {
      return new Symbol(type, yyline, yycolumn);
    }

    private Symbol symbol(int type, Object value) {
      return new Symbol(type, yyline, yycolumn, value);
    }

    private void log(String msg) {
      if (debug_) {
        System.err.print(msg);
      }
    }

    //Remove a possible extra '}' to close a box name.
    //This is a bit dodgy, but I think is the simplest way to do this.
    private String removeRbrace(String name) {
      int bCount = 0; //the number of open brackets
      String result = new String(name);

      for (int i = 0; i < name.length(); i++) {
        if (name.charAt(i) == STARTGLUE) {
          bCount++;
        }
        else if (name.charAt(i) == ENDGLUE) {
          bCount--;
        }
      }

      //if the name includes the '}' to close the box name
      if (bCount == -1) {
        result = new String(name.substring(0, name.lastIndexOf(ENDGLUE)));
        inBoxName = false;
      }
      return result;
    }

    //converts all single up and down characters to normal up and down
    //e.g. name_1 to name_{1}
    private String fixGlue(String name) {
      String result = new String();

      for (int i = 0; i < name.length(); i++) {
        if (name.charAt(i) == STROKE_USCORE || name.charAt(i) == UPTOK) {
          if ((i == 0 || (i > 0 && name.charAt(i - 1) != '\\')) &&
              name.charAt(i + 1) != STARTGLUE) {

            result += name.substring(i, i + 1) + STARTGLUE +
                      name.substring(i + 1, i + 2) + ENDGLUE;
            i++;
          }
          else {
            result += name.substring(i, i + 1);
          }
        }
        else {
          result += name.substring(i, i + 1);
        }
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

OZTOOLKITSYMBOL = "\\bool" | "\\copyright" | "\\poly" | "\\oid" | "\\classuni"

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
VARG = "\\varg" | "\\_"

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
ZED = "\\begin" {SoftWhiteSpace}* "{zed}" | "\\begin" {SoftWhiteSpace}* "{syntax}"

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

WORDPART = {WORDGLUE} ( {ALPHASTR} | {SYMBOL}* )
ALPHASTR = ( {LETTER} | {DIGIT} )*

//Section names can be used as file names
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
                          inBoxName = true;
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
                          inBoxName = true;
                          log(yytext());
                          inOzClass = true;
                          return symbol(LatexSym.CLASS);
                        }

  [a-zA-Z0-9]+          {
                          log(yytext());
                          return symbol(LatexSym.NARRWORD, yytext());
                        }


  {Comment}             {
                          log(yytext());
                          return symbol(LatexSym.NARRWORD, yytext());
                        }

  //whitespace
  {HardWhiteSpace}      {
                          log(yytext());
                          return symbol(LatexSym.NARRWORD, yytext());
                        }

  {SoftWhiteSpace}      {
                          log(yytext());
                          return symbol(LatexSym.NARRWORD, yytext());
                        } 

}

<OZ> {

  //basic types
  {POWER}               { log(yytext()); return symbol(LatexSym.POWER, yytext()); }

  //Greek chars
  {DELTA}               { log(yytext()); return symbol(LatexSym.DELTA); }
  {THETA}               { log(yytext()); return symbol(LatexSym.THETA); }
  {MU}                  { log(yytext()); return symbol(LatexSym.MU); }
  {LAMBDA}              { log(yytext()); return symbol(LatexSym.LAMBDA); }


  {INSTROKE}            { log(yytext()); return symbol(LatexSym.INSTROKE); }
  {OUTSTROKE}           { log(yytext()); return symbol(LatexSym.OUTSTROKE); }
  {NEXTSTROKE}          { log(yytext()); return symbol(LatexSym.NEXTSTROKE); } 
  {NUMSTROKE}           {
                          String numStroke = fixGlue(yytext());
                          log(numStroke);
                          return symbol(LatexSym.NUMSTROKE, numStroke);
                        }

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
  {LBRACE}              { log(yytext()); /* do nothing */ }

  {RBRACE}              { 
                          log(yytext());
                          if (inWordGlue) {
                            inWordGlue = false;
                            return symbol(LatexSym.NAME, yytext());
                          }
                          else if (inBoxName) {                            
                            inBoxName = false;
                          }
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
  {ZPROJECT}             { log(yytext()); return symbol(LatexSym.ZPROJECT); }

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
  //"begin" box characters for OZ local definitions
  {GENAX}               { log(yytext()); return symbol(LatexSym.GENAX); }
  {AX}                  { log(yytext()); return symbol(LatexSym.AX); }
  {ZED}                 { log(yytext()); return symbol(LatexSym.ZED); }

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
  {INITWORD}            { log(yytext()); return symbol(LatexSym.INITWORD, yytext()); }
  {SCHEMA}              {
                          log(yytext());
                          inBoxName = true;
                          return symbol(LatexSym.SCHEMA);
                        }
  {OPSCHEMA}            {
                          log(yytext());
                          inBoxName = true;
                          return symbol(LatexSym.OPSCHEMA);
                        }

  //Object-Z paragraph chars
  {VISIBILITY}          { log(yytext()); return symbol(LatexSym.VISIBILITY); }
  {INHERITS}            { log(yytext()); return symbol(LatexSym.INHERITS); }

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
  {NUMBER}              {
                          log(yytext());
                          return symbol(LatexSym.NUMBER, 
                                        new Integer(yytext()));
                        }

  {NAME}                {
                          String name = fixGlue(yytext());

                          //if the name is a schema or class name, return a
                          //BOXNAME to avoid confusion in the SmartScanner
                          if (inBoxName) {
                            String boxName = removeRbrace(name);
                            log(name);
                            return symbol(LatexSym.BOXNAME, boxName); 
                          }
                          //if it is only an underscore, it is a optemp arg
                          else if (yytext().equals(USCORE)) {
                            log(name);
                            return symbol(LatexSym.VARG);
                          }
                          //if it is the start of a wordglue, the next RBRACE must
                          //be a end glue, so set inWordGlue to true
                          else if (yytext().equals(UPGLUE) || yytext().equals(DOWNGLUE)) {
                            log(yytext());
                            inWordGlue = true;
                            return symbol(LatexSym.NAME, yytext());
                          }
                          else {
                            String noBraceName = removeRbrace(name);
                            log(name);
                            return symbol(LatexSym.NAME, noBraceName);
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
