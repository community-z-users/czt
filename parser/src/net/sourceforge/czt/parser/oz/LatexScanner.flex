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

import java.util.List;
import java.util.ArrayList;

import net.sourceforge.czt.util.CztException;

%%

%class LatexScanner
%public
%unicode
%cupsym Sym
%cup
%line
%column

%{
    /** Stroke characters */
    public final static char INSTROKE = '!';
    public final static char OUTSTROKE = '?';
    public final static char NEXTSTROKE = '\'';
    public final static char STROKE_USCORE = '_';
    public final static String NUMSTROKE_REGEX = "_\\{[0-9]\\}";

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


    public static List getNameAndStroke(String name)
    {
      List result = new ArrayList();
      String baseName = null;
      List strokes = new ArrayList();

      int finalStroke = name.length();

      for (int i = name.length() - 1;
           i >= 0 &&
           (name.charAt(i) == INSTROKE ||
            name.charAt(i) == OUTSTROKE ||
            name.charAt(i) == NEXTSTROKE ||
            (i > 3 &&
             name.substring(i - 3, i + 1).matches(NUMSTROKE_REGEX)));
           i--) {

        if (name.charAt(i) == ENDGLUE) {
          strokes.add(0, getNumStroke(name.substring(i - 3, i + 1)));
          i -= 3;  //skip the rest
        }
        else {
          strokes.add(0, getStroke(name.substring(i, i + 1)));
        }
        finalStroke = i;
      }

      baseName = name.substring(0, finalStroke);

      result.add(baseName);
      result.add(strokes);
      return result;
    }

    /**
     * Returns the symbol number for a given stroke
     */
    private static Symbol getStroke(String stroke)
    {
      Symbol result = null;

      switch (stroke.charAt(0))
      {
        case INSTROKE:
          result = new Symbol(Sym.INSTROKE);
          break;
        case OUTSTROKE:
          result = new Symbol(Sym.OUTSTROKE);
          break;
        case NEXTSTROKE:
          result = new Symbol(Sym.NEXTSTROKE);
          break;
        default:        
          System.err.println("Invalid stroke:" + stroke);
      }
      return result;
    }

    /**
     * Returns the symbol number for a given number stroke
     */
    protected static Symbol getNumStroke(String stroke)
    {
      Symbol result = null;

      switch (stroke.charAt(0))
      {
        case STROKE_USCORE:
        case UPTOK:
          result = new Symbol(Sym.NUMSTROKE,
                              new Integer(stroke.substring(2, 3)));
          break;
        default:
          System.err.println("Invalid number stroke:" + stroke);
      }
      return result;
    }

    /**
     * Extracts a number from a number stroke.
     */
    protected Integer extractNum(String numStroke)
    {
      Integer result = null;

      if (numStroke.startsWith(DOWNGLUE)) {
        result = new Integer(numStroke.substring(2, 3));
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

SYMBOL = {BAR} | {ANDALSO} | {CONJECTURE} | {AND} | {OR} | {IMP} | {IFF} | {NOT} |
        {ALL} | {EXI} | {CROSS} | {SLASH} | {EQUALS} | {MEM} | {COLON} |
        {SEMICOLON} | {COMMA} | {DOT} | {SPOT} |
        {ZHIDE} | {ZPROJ} | {ZCOMP} | {ZPIPE} | {PLUS} |
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

LLATEXBRACE = "{"
RLATEXBRACE = "}"

USCORE = "\\_"

LPAREN = "("
RPAREN = ")"
LSQUARE = "["
RSQUARE = "]" 
LBIND = "\\lblot"
RBIND = "\\rblot"
LDATA = "\\ldata"
RDATA = "\\rdata"
LBRACE = "\\{"
RBRACE = "\\}"

//Z symbols
BAR = "|" | "\\cbar" | "\\where"
ANDALSO = "&"
CONJECTURE = "\\models?"
AND = "\\land"
OR = "\\lor"
IMP = "\\implies"
IFF = "\\iff"
NOT = "\\lnot"
ALL = "\\forall"
EXI = "\\exists"
CROSS = "\\cross"
SLASH = "/"
EQUALS = "="
MEM = "\\in"
COLON = ":"
SEMICOLON = ";"
COMMA = ","
DOT = "."
SPOT = "@"
ZHIDE = "\\hide"
ZPROJ = "\\project"
ZCOMP = "\\semi"
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
ZPRE = "\\pre"
RELATION = "\\relation"
FUNCTION = "\\function"
GENERIC = "\\generic"
LEFTASSOC = "\\leftassoc"
RIGHTASSOC = "\\rightassoc"

LISTARG = "\\listarg"
ARG = "\\varg" | "\\_"

DEFFREE = "::=" | "\\ddef"
DEFEQUAL = "==" | "\\defs"

EXIONE = {EXI} ( {DOWN} "1" {ENDGLUE} |  {SINGLEDOWN} "1" )

//box characters
END = "\\end" {SoftWhiteSpace}* 
      ( "{axdef}" | "{schema}" | "{gendef}" | "{syntax}" | "{zed}" |
        "{state}" | "{init}" | "{op}" | "{localdef}" | "{zsection}" )

AX = "\\begin" {SoftWhiteSpace}* "{axdef}"
SCH = "\\begin" {SoftWhiteSpace}* "{schema}"
GENAX = "\\begin" {SoftWhiteSpace}* "{gendef}"

//Z paragraphs
ZED = "\\begin" {SoftWhiteSpace}* "{zed}" |
      "\\begin" {SoftWhiteSpace}* "{syntax}"

//Z sections
ZSECTION = "\\begin" {SoftWhiteSpace}* "{zsection}"

//object-z box characters
CLASS = "\\begin" {SoftWhiteSpace}* "{class}"
STATE = "\\begin" {SoftWhiteSpace}* "{state}"
INIT = "\\begin" {SoftWhiteSpace}* ( "{init}" | "{schema}" {SoftWhiteSpace}* "{\Init}" )
INITWORD = "\\Init"
OPSCH = "\\begin" {SoftWhiteSpace}* "{op}"
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

NUMERAL = {DIGIT}+
STROKE = {STROKECHAR} | {NUMSTROKE}
DECORWORD =  {WORD} {STROKE}*
WORD =  {WORDPART}+ |
        {LETTER} {ALPHASTR} {WORDPART}* |
        {SYMBOL}+ {WORDPART}*

WORDPART = {WORDGLUE} ( {ALPHASTR} | {SYMBOL}* )
ALPHASTR = ( {LETTER} | {DIGIT} )*

//Section names can be used as file names
SECTIONNAME = {LATIN} ({LATIN} | {USCORE} | {SLASH})*

%state ZSECTION OZ CLASSCOMMENT

%%

<YYINITIAL> {

  //Z section
  {ZSECTION}            {
                          yybegin(ZSECTION);
                          log(yytext());
                          return symbol(Sym.ZED);
                        }

  //Box characters
  {AX}                  {
                          yybegin(OZ);
                          log(yytext()); 
                          return symbol(Sym.AX);
                        }

  {SCH}                 { 
                          yybegin(OZ);
                          inBoxName = true;
                          log(yytext());
                          return symbol(Sym.SCH);
                        }

  {GENAX}               {
                          yybegin(OZ);
                          log(yytext());
                          return symbol(Sym.GENAX);
                        }

  //Z paragraphs
  {ZED}                 {
                          yybegin(OZ);
                          log(yytext());
                          return symbol(Sym.ZED);
                        }

  //Class box
  {CLASS}               {
                          yybegin(OZ);
                          inBoxName = true;
                          log(yytext());
                          inOzClass = true;
                          return symbol(Sym.CLASS);
                        }

  [a-zA-Z0-9]+          {
                          log(yytext());
                          return symbol(Sym.TEXT, yytext());
                        }


  {Comment}             {
                          log(yytext());
                          return symbol(Sym.TEXT, yytext());
                        }

  //whitespace
  {HardWhiteSpace}      {
                          log(yytext());
                          return symbol(Sym.TEXT, yytext());
                        }

  {SoftWhiteSpace}      {
                          log(yytext());
                          return symbol(Sym.TEXT, yytext());
                        } 

}

<OZ> {

  //basic types
  {POWER}               { log(yytext()); return symbol(Sym.POWER); }

  //Greek chars
  {DELTA}               { log(yytext()); return symbol(Sym.DELTA); }
  {THETA}               { log(yytext()); return symbol(Sym.THETA); }
  {MU}                  { log(yytext()); return symbol(Sym.MU); }
  {LAMBDA}              { log(yytext()); return symbol(Sym.LAMBDA); }


  {INSTROKE}            { log(yytext()); return symbol(Sym.INSTROKE); }
  {OUTSTROKE}           { log(yytext()); return symbol(Sym.OUTSTROKE); }
  {NEXTSTROKE}          { log(yytext()); return symbol(Sym.NEXTSTROKE); } 
  {NUMSTROKE}           {
                          String numStroke = fixGlue(yytext());
                          log(numStroke);
                          Integer iStroke = extractNum(numStroke);
                          return symbol(Sym.NUMSTROKE, iStroke);
                        }

  //Brackets etc
  {LPAREN}              { log(yytext()); return symbol(Sym.LPAREN); }
  {RPAREN}              { log(yytext()); return symbol(Sym.RPAREN); }
  {LSQUARE}             { log(yytext()); return symbol(Sym.LSQUARE); }
  {RSQUARE}             { log(yytext()); return symbol(Sym.RSQUARE); }
  {LBIND}               { log(yytext()); return symbol(Sym.LBIND); }
  {RBIND}               { log(yytext()); return symbol(Sym.RBIND); }
  {LDATA}               { log(yytext()); return symbol(Sym.LDATA); }
  {RDATA}               { log(yytext()); return symbol(Sym.RDATA); }
  {LBRACE}              { log(yytext()); return symbol(Sym.LBRACE); }
  {RBRACE}              { log(yytext()); return symbol(Sym.RBRACE); }

  //Latex symbols
  {LLATEXBRACE}         { log(yytext()); /* do nothing */ }

  {RLATEXBRACE}         { 
                          log(yytext());
                          if (inWordGlue) {
                            inWordGlue = false;
                            return symbol(Sym.DECORWORD, yytext());
                          }
                          else if (inBoxName) {                            
                            inBoxName = false;
                          }
                        }

  //Core symbols
  {BAR}                 { log(yytext()); return symbol(Sym.BAR); }
  {ANDALSO}             { log(yytext()); return symbol(Sym.ANDALSO); }
  {CONJECTURE}          { log(yytext()); return symbol(Sym.CONJECTURE); }
  {AND}                 { log(yytext()); return symbol(Sym.AND); }
  {OR}                  { log(yytext()); return symbol(Sym.OR); }
  {IMP}                 { log(yytext()); return symbol(Sym.IMP); }
  {IFF}                 { log(yytext()); return symbol(Sym.IFF); }
  {NOT}                 { log(yytext()); return symbol(Sym.NOT); }
  {ALL}                 { log(yytext()); return symbol(Sym.ALL); }
  {EXI}                 { log(yytext()); return symbol(Sym.EXI); }
  {EXIONE}              { log(yytext()); return symbol(Sym.EXIONE); }
  {CROSS}               { log(yytext()); return symbol(Sym.CROSS); }
  {SLASH}               { log(yytext()); return symbol(Sym.SLASH); }
  {EQUALS}              { log(yytext()); return symbol(Sym.EQUALS); }
  {MEM}                 { log(yytext()); return symbol(Sym.MEM); }
  {COLON}               { log(yytext()); return symbol(Sym.COLON); }
  {SEMICOLON}           { log(yytext()); return symbol(Sym.SEMICOLON); }
  {COMMA}               { log(yytext()); return symbol(Sym.COMMA); }
  {DOT}                 { log(yytext()); return symbol(Sym.DOT); }
  {SPOT}                { log(yytext()); return symbol(Sym.SPOT); }
  {ZCOMP}               { log(yytext()); return symbol(Sym.ZCOMP); }
  {ZHIDE}               { log(yytext()); return symbol(Sym.ZHIDE); }
  {ZPIPE}               { log(yytext()); return symbol(Sym.ZPIPE); }
  {ZPROJ}               { log(yytext()); return symbol(Sym.ZPROJ); }

  //Other symbols
  {NL}                  { log(yytext()); return symbol(Sym.NL); }
  {TRUE}                { log(yytext()); return symbol(Sym.TRUE); }
  {FALSE}               { log(yytext()); return symbol(Sym.FALSE); }
  {LET}                 { log(yytext()); return symbol(Sym.LET); }
  {IF}                  { log(yytext()); return symbol(Sym.IF); }
  {THEN}                { log(yytext()); return symbol(Sym.THEN); }
  {ELSE}                { log(yytext()); return symbol(Sym.ELSE); }
  {ZPRE}                { log(yytext()); return symbol(Sym.ZPRE); }
  {RELATION}            { log(yytext()); return symbol(Sym.RELATION); }
  {FUNCTION}            { log(yytext()); return symbol(Sym.FUNCTION); }
  {GENERIC}             { log(yytext()); return symbol(Sym.GENERIC); }
  {LEFTASSOC}           { log(yytext()); return symbol(Sym.LEFTASSOC); }
  {RIGHTASSOC}          { log(yytext()); return symbol(Sym.RIGHTASSOC); }

  {LISTARG}             { log(yytext()); return symbol(Sym.LISTARG); }
  {ARG}                 { log(yytext()); return symbol(Sym.ARG); }

  {DEFFREE}             { log(yytext()); return symbol(Sym.DEFFREE); }
  {DEFEQUAL}            { log(yytext()); return symbol(Sym.DEFEQUAL); }

  //Box characters
  //"begin" box characters for OZ local definitions
  {GENAX}               { log(yytext()); return symbol(Sym.GENAX); }
  {AX}                  { log(yytext()); return symbol(Sym.AX); }
  {ZED}                 { log(yytext()); return symbol(Sym.ZED); }

  {END}                 { if (!inOzClass) {
                              yybegin(YYINITIAL);
                          }
                          log(yytext()); 
                          return symbol(Sym.END);
                        }

  {ENDCLASS}            {
                          yybegin(YYINITIAL);
                          log(yytext()); 
                          return symbol(Sym.END);
                        }

  {STATE}               { log(yytext()); return symbol(Sym.STATE); }
  {INIT}                { log(yytext()); return symbol(Sym.INIT); }
  {INITWORD}            { log(yytext()); return symbol(Sym.INITWORD, yytext()); }
  {SCH}                 {
                          log(yytext());
                          inBoxName = true;
                          return symbol(Sym.SCH);
                        }
  {OPSCH}               {
                          log(yytext());
                          inBoxName = true;
                          return symbol(Sym.OPSCH);
                        }

  //Object-Z paragraph chars
  {VISIBILITY}          { log(yytext()); return symbol(Sym.VISIBILITY); }
  {INHERITS}            { log(yytext()); return symbol(Sym.INHERITS); }


  //Object-Z operation expressions
  {DCNJ}                { log(yytext()); return symbol(Sym.DCNJ); }
  {DGCH}                { log(yytext()); return symbol(Sym.DGCH); }
  {DSQC}                { log(yytext()); return symbol(Sym.DSQC); }

  {PARALLEL}            { log(yytext()); return symbol(Sym.PARALLEL); }
  {ASSOCPARALLEL}       { log(yytext()); return symbol(Sym.ASSOCPARALLEL); }
  {GCH}                 { log(yytext()); return symbol(Sym.GCH); }

  //Object-Z class comments
  {CLASSCOM}            {
                          yybegin(CLASSCOMMENT);
                          log(yytext());
                          return symbol(Sym.CLASSCOM);
                        }

  //literals
  {NUMERAL}             {
                          log(yytext());
                          return symbol(Sym.NUMERAL, 
                                        new Integer(yytext()));
                        }

  {DECORWORD}           {
                          String name = fixGlue(yytext());

                          //if the name is a schema or class name, return a
                          //BOXNAME to avoid confusion in the SmartScanner
                          if (inBoxName) {
                            String boxName = removeRbrace(name);
                            log(name);
                            //return symbol(Sym.BOXNAME, boxName); 
return symbol(Sym.DECORWORD, boxName); 
                          }
                          //if it is only an underscore, it is a optemp arg
                          else if (yytext().equals(USCORE)) {
                            log(name);
                            return symbol(Sym.ARG);
                          }
                          //if it is the start of a wordglue, the next RLATEXBRACE must
                          //be a end glue, so set inWordGlue to true
                          else if (yytext().equals(UPGLUE) || yytext().equals(DOWNGLUE)) {
                            log(yytext());
                            inWordGlue = true;
                            return symbol(Sym.DECORWORD, yytext());
                          }
                          else {
                            String noBraceName = removeRbrace(name);
                            log(name);
                            return symbol(Sym.DECORWORD, noBraceName);
                          }
                        }

  //whitespace
  {HardWhiteSpace}      { /* ignore */ }        
  {SoftWhiteSpace}      { log(yytext()); /* ignore */ }

  {Comment}             { /* ignore */ }
}

<ZSECTION> {

  {SECTION}             { log(yytext()); return symbol(Sym.SECTION); }
  {PARENTS}             { log(yytext()); return symbol(Sym.PARENTS); }
  {COMMA}               { log(yytext()); return symbol(Sym.COMMA); }

  {SECTIONNAME}         { log(yytext());
                          return symbol(Sym.DECORWORD, 
                                        new String(yytext())); }

  {END}                 {
                          yybegin(YYINITIAL);
                          log(yytext());
                          return symbol(Sym.END);
                        }

  {NL}                  { log(yytext()); /* ignore */ }

  //whitespace
  {HardWhiteSpace}      { log(yytext()); /* ignore */ }        
  {SoftWhiteSpace}      { log(yytext()); /* ignore */ }

  {Comment}             { /* ignore */ }
}

<CLASSCOMMENT> {

  {ENDCLASSCOM}         {
                          yybegin(YYINITIAL);
                          log(yytext());
                          return symbol(Sym.ENDCLASSCOM);
                        }

  . | \n                { log(yytext()); return symbol(Sym.CLASSCOMWORD);
                        }

}

//error fallback and narr para
. | \n                  {
                          //if this is a narr para
                          if (yystate() == YYINITIAL) {
                              log(yytext()); 
                              return symbol(Sym.TEXT, yytext());
                          } else {
                              throw new Error("Illegal character \"" +
                                              yytext() + "\"");
                          }
                        }
