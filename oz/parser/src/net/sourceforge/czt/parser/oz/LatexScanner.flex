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
          result = new Symbol(LatexSym.INSTROKE);
          break;
        case OUTSTROKE:
          result = new Symbol(LatexSym.OUTSTROKE);
          break;
        case NEXTSTROKE:
          result = new Symbol(LatexSym.NEXTSTROKE);
          break;
        default:        
          //TODO: throw exception
          System.err.println("NO MATCH IN getStroke");
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
          result = new Symbol(LatexSym.NUMSTROKE,
                              new Integer(stroke.substring(2, 3)));
          break;
        default:
          //TODO: throw exception
          System.err.println("NO MATCH IN getNumStroke");
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
ZED = "\\begin" {SoftWhiteSpace}* "{zed}" | "\\begin" {SoftWhiteSpace}* "{syntax}"


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
                          return symbol(LatexSym.ZSECTION);
                        }

  //Box characters
  {AX}                  {
                          yybegin(OZ);
                          log(yytext()); 
                          return symbol(LatexSym.AX);
                        }

  {SCH}                 { 
                          yybegin(OZ);
                          inBoxName = true;
                          log(yytext());
                          return symbol(LatexSym.SCH);
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
                          return symbol(LatexSym.TEXT, yytext());
                        }


  {Comment}             {
                          log(yytext());
                          return symbol(LatexSym.TEXT, yytext());
                        }

  //whitespace
  {HardWhiteSpace}      {
                          log(yytext());
                          return symbol(LatexSym.TEXT, yytext());
                        }

  {SoftWhiteSpace}      {
                          log(yytext());
                          return symbol(LatexSym.TEXT, yytext());
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
                          Integer iStroke = extractNum(numStroke);
                          return symbol(LatexSym.NUMSTROKE, iStroke);
                        }

  //Brackets etc
  {LPAREN}              { log(yytext()); return symbol(LatexSym.LPAREN); }
  {RPAREN}              { log(yytext()); return symbol(LatexSym.RPAREN); }
  {LSQUARE}             { log(yytext()); return symbol(LatexSym.LSQUARE); }
  {RSQUARE}             { log(yytext()); return symbol(LatexSym.RSQUARE); }
  {LBIND}               { log(yytext()); return symbol(LatexSym.LBIND); }
  {RBIND}               { log(yytext()); return symbol(LatexSym.RBIND); }
  {LDATA}               { log(yytext()); return symbol(LatexSym.LDATA); }
  {RDATA}               { log(yytext()); return symbol(LatexSym.RDATA); }
  {LBRACE}              { log(yytext()); return symbol(LatexSym.LBRACE); }
  {RBRACE}              { log(yytext()); return symbol(LatexSym.RBRACE); }

  //Latex symbols
  {LLATEXBRACE}         { log(yytext()); /* do nothing */ }

  {RLATEXBRACE}         { 
                          log(yytext());
                          if (inWordGlue) {
                            inWordGlue = false;
                            return symbol(LatexSym.DECORWORD, yytext());
                          }
                          else if (inBoxName) {                            
                            inBoxName = false;
                          }
                        }

  //Core symbols
  {BAR}                 { log(yytext()); return symbol(LatexSym.BAR); }
  {ANDALSO}             { log(yytext()); return symbol(LatexSym.ANDALSO); }
  {CONJECTURE}          { log(yytext()); return symbol(LatexSym.CONJECTURE); }
  {AND}                 { log(yytext()); return symbol(LatexSym.AND); }
  {OR}                  { log(yytext()); return symbol(LatexSym.OR); }
  {IMP}                 { log(yytext()); return symbol(LatexSym.IMP); }
  {IFF}                 { log(yytext()); return symbol(LatexSym.IFF); }
  {NOT}                 { log(yytext()); return symbol(LatexSym.NOT); }
  {ALL}                 { log(yytext()); return symbol(LatexSym.ALL); }
  {EXI}                 { log(yytext()); return symbol(LatexSym.EXI); }
  {EXIONE}              { log(yytext()); return symbol(LatexSym.EXIONE); }
  {CROSS}               { log(yytext()); return symbol(LatexSym.CROSS); }
  {SLASH}               { log(yytext()); return symbol(LatexSym.SLASH); }
  {EQUALS}              { log(yytext()); return symbol(LatexSym.EQUALS); }
  {MEM}                 { log(yytext()); return symbol(LatexSym.MEM); }
  {COLON}               { log(yytext()); return symbol(LatexSym.COLON); }
  {SEMICOLON}           { log(yytext()); return symbol(LatexSym.SEMICOLON); }
  {COMMA}               { log(yytext()); return symbol(LatexSym.COMMA); }
  {DOT}                 { log(yytext()); return symbol(LatexSym.DOT); }
  {SPOT}                { log(yytext()); return symbol(LatexSym.SPOT); }
  {ZCOMP}               { log(yytext()); return symbol(LatexSym.ZCOMP); }
  {ZHIDE}               { log(yytext()); return symbol(LatexSym.ZHIDE); }
  {ZPIPE}               { log(yytext()); return symbol(LatexSym.ZPIPE); }
  {ZPROJ}               { log(yytext()); return symbol(LatexSym.ZPROJ); }

  //Other symbols
  {NL}                  { log(yytext()); return symbol(LatexSym.NL); }
  {TRUE}                { log(yytext()); return symbol(LatexSym.TRUE); }
  {FALSE}               { log(yytext()); return symbol(LatexSym.FALSE); }
  {LET}                 { log(yytext()); return symbol(LatexSym.LET); }
  {IF}                  { log(yytext()); return symbol(LatexSym.IF); }
  {THEN}                { log(yytext()); return symbol(LatexSym.THEN); }
  {ELSE}                { log(yytext()); return symbol(LatexSym.ELSE); }
  {ZPRE}                { log(yytext()); return symbol(LatexSym.ZPRE); }
  {RELATION}            { log(yytext()); return symbol(LatexSym.RELATION); }
  {FUNCTION}            { log(yytext()); return symbol(LatexSym.FUNCTION); }
  {GENERIC}             { log(yytext()); return symbol(LatexSym.GENERIC); }
  {LEFTASSOC}           { log(yytext()); return symbol(LatexSym.LEFTASSOC); }
  {RIGHTASSOC}          { log(yytext()); return symbol(LatexSym.RIGHTASSOC); }

  {LISTARG}             { log(yytext()); return symbol(LatexSym.LISTARG); }
  {ARG}                 { log(yytext()); return symbol(LatexSym.ARG); }

  {DEFFREE}             { log(yytext()); return symbol(LatexSym.DEFFREE); }
  {DEFEQUAL}            { log(yytext()); return symbol(LatexSym.DEFEQUAL); }

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
  {SCH}                 {
                          log(yytext());
                          inBoxName = true;
                          return symbol(LatexSym.SCH);
                        }
  {OPSCH}               {
                          log(yytext());
                          inBoxName = true;
                          return symbol(LatexSym.OPSCH);
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
  {NUMERAL}             {
                          log(yytext());
                          return symbol(LatexSym.NUMERAL, 
                                        new Integer(yytext()));
                        }

  {DECORWORD}           {
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
                            return symbol(LatexSym.ARG);
                          }
                          //if it is the start of a wordglue, the next RLATEXBRACE must
                          //be a end glue, so set inWordGlue to true
                          else if (yytext().equals(UPGLUE) || yytext().equals(DOWNGLUE)) {
                            log(yytext());
                            inWordGlue = true;
                            return symbol(LatexSym.DECORWORD, yytext());
                          }
                          else {
                            String noBraceName = removeRbrace(name);
                            log(name);
                            return symbol(LatexSym.DECORWORD, noBraceName);
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
                          return symbol(LatexSym.DECORWORD, 
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

  . | \n                { log(yytext()); return symbol(LatexSym.CLASSCOMWORD);
                        }

}

//error fallback and narr para
. | \n                  {
                          //if this is a narr para
                          if (yystate() == YYINITIAL) {
                              log(yytext()); 
                              return symbol(LatexSym.TEXT, yytext());
                          } else {
                              throw new Error("Illegal character \"" +
                                              yytext() + "\"");
                          }
                        }
