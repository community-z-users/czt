
/* --------------------------Usercode Section------------------------ */
package net.sourceforge.czt.scanner;

import java_cup.runtime.*;
      
%%
   
/* -----------------Options and Declarations Section----------------- */
   
%class LatexLexer
%unicode
%line
%column
%cup
   
%{   
    /* To create a new java_cup.runtime.Symbol with information about
       the current token, the token will have no value in this
       case. */
    private Symbol symbol(int type) {
        return new Symbol(type, yyline, yycolumn);
    }
    
    /* Also creates a new java_cup.runtime.Symbol with information
       about the current token, but this object has a value. */
    private Symbol symbol(int type, Object value) {
        return new Symbol(type, yyline, yycolumn, value);
    }

    private void log(String message) {
	System.out.print(message + " ");
    }
%}
   

/* Macro Declarations */
LineTerminator = \r|\n|\r\n
WhiteSpace = " " | "\t"

SoftWhitSpace = {LineTerminator} | {WhiteSpace}
HardSpace = "~" | "\\," | "\\!" | "\\ " | "\\;" | "\\:" | "\\tl" | "\\t2" | "\\t3" | "\\t4" | "\\t5" | "\\t6" | "\\t7" | "\\t8" | "\\t9"

DIGIT = [0-9]
LETTER = {LATIN} | {GREEK} | {OTHERLETTER}
LATIN = [A-Za-z]
GREEK = {DELTA} | {XI} | {THETA} | {LAMBDA} | {MU}
DELTA = "\\Delta"
XI = "\\Xi"
THETA = "\\theta"
LAMBDA = "\\lambda"
MU = "\\mu"
OTHERLETTER = {NAT} | {POWER}
NAT = "\\nat"
POWER = "\\power"
STROKECHAR = {PRIME} | {OUTSTROKE} | {INSTROKE}
PRIME = "\u02B9"
OUTSTROKE = "\u0021"
INSTROKE = "\u003F"
WORDGLUE = {NE} | {SW} | {SE} | {NW} | {LL}
NE = "^{"
SW = "}"
SE = "_{"
NW = "}"
LL = "\u005F"
LPAREN = "\u0028"
RPAREN = "\u0029"
LSQUARE = "\u005B"
RSQUARE = "\u005D"
LBRACE = "\\{"
RBRACE = "\\}"
LBIND = "\\lblot"
RBIND = "\\rblot"
LDATA = "\\ldata"
RDATA = "\\rdata"
SYMBOL = {CORESYMBOL} | {TOOLKITSYMBOL}
CORESYMBOL = {VL} | {AMP} | {VDASH} | {AND} | {OR} | {IMP} | {IFF} | {NOT} | {ALL} | {EXI} | {CROSS} | {SOLIDUS} | {EQUALS} | {MEM} | {COLON} | {SEMICOLON} | {COMMA} | {DOT} | {SPOT} | {ZHIDE} | {ZPROJ} | {ZCOMP} | {ZPIPE} | {PLUS} | {TYPECOLON}
VL = "\u007C"
AMP = "\u0026"
VDASH = "\\vdash"
AND = "\\land"
OR = "\\lor"
IMP = "\\implies"
IFF = "\\iff"
NOT = "\\lnot"
ALL = "\\forall"
EXI = "\\exists"
CROSS = "\\cross"
SOLIDUS = "\u002F"
EQUALS = "\u003D"
MEM = "\\in"
COLON = "\u003A"
SEMICOLON = "\u003B"
COMMA = "\u002C"
DOT = "\u002E"
SPOT = "@"
ZHIDE = "\\hide"
ZPROJ = "\\project"
ZCOMP = "\\semi"
ZPIPE = "\\pipe"
PLUS = "\u002B"
TYPECOLON = "\u2982"
TOOLKITSYMBOL = {REL} | {FUN} | {NEQ} | {NOTMEM} | {EMPTYSET} | {SUBSETEQ} | {SUBSET} | {CUP} | {CAP} | {SETMINUS} | {SYMDIFF} | {BIGCUP} | {BIGCAP} | {MAPSTO} | {COMP} | {CIRC} | {DRES} | {RRES} | {NDRES} | {NRRES} | {TILDE} | {LIMG} | {RIMG} | {OPLUS} | {PFUN} | {PINJ} | {INJ} | {PSURJ} | {SURJ} | {BIJ} | {FFUN} | {FINJ} | {NUM} | {NEG} | {MINUS} | {LEQ} | {LESS} | {GEQ} | {GREATER} | {NUMBER} | {LANGLE} | {RANGLE} | {CAT} | {EXTRACT} | {FILTER}
REL = "\\rel"
FUN = "\\fun"
NEQ = "\\neq"
NOTMEM = "\\notin"
EMPTYSET = "\\emptyset"
SUBSETEQ = "\\subseteq"
SUBSET = "\\subset"
CUP = "\\cup"
CAP = "cap"
SETMINUS = "\\setminus"
SYMDIFF = "\\symdiff"
BIGCUP = "\\bigcup"
BIGCAP = "\\bigcap"
MAPSTO = "\\mapsto"
COMP = "\\comp"
CIRC = "\\circ"
DRES = "\\dres"
RRES = "\\rres"
NDRES = "\\ndres"
NRRES = "\\nrres"
TILDE = "~"
LIMG = "\\limg"
RIMG = "\\rimg"
OPLUS = "\\oplus"
PFUN = "\\pfun"
PINJ = "\\pinj"
INJ = "\\inj"
PSURJ = "\\psurj"
SURJ = "\\surj"
BIJ = "\\bij"
FFUN = "\\ffun"
FINJ = "\\finj"
NUM = "\\num"
NEG = "\\negate"
MINUS = "-"
LEQ = "\\leq"
LESS = "\u003C"
GEQ = "\\geq"
GREATER = "\u003E"
NUMBER = "\\#"
LANGLE = "\\langle"
RANGLE = "\\rangle"
CAT = "\\cat"
EXTRACT = "extract"
FILTER = "filter"

DECORWORD = {WORD} {STROKE}*
WORD =   {WORDPART}+ | {LETTER} {ALPHASTR} {WORDPART}* | {SYMBOL}+ {WORDPART}*
WORDPART = {WORDGLUE} ( {ALPHASTR} | {SYMBOL}* )
ALPHASTR = ({LETTER} | {DIGIT})*
NUMERAL = {DIGIT}+
STROKE = {STROKECHAR} | {SE} {DIGIT} {NW}


%state ZED

%%
/* ------------------------Lexical Rules Section---------------------- */
   
<YYINITIAL> {
  "\\begin{axdef}"                      { yybegin(ZED);
                                          log("AXCHAR"); }
  "\\begin{gendef}"                     { yybegin(ZED);
                                          log("AXCHAR GENCHAR");
                                        }
  "\\begin{schema}{" [^}]* "}"         { yybegin(ZED);
                                          log("SCHCHAR"); }
  "\\begin{zed}"                        { yybegin(ZED);
                                          log(" "); }
  [^]                                   { log(yytext()); }
}

<ZED> {
  "\\end{axdef}"                        { yybegin(YYINITIAL);
                                          log("ENDCHAR"); }
  "\\end{gendef}"                       { yybegin(YYINITIAL);
                                          log("ENDCHAR"); }
  "\\end{schema}"                       { yybegin(YYINITIAL);
                                          log("ENDCHAR"); }
  "\\end{zed}"                          { yybegin(YYINITIAL);
                                          log("ENDCHAR"); }
  "\\where"                             { log("BAR"); return symbol(sym.BAR); }

  {LPAREN}                      { log("LPAREN"); return symbol(sym.LPAREN); }
  {RPAREN}                      { log("RPAREN"); return symbol(sym.RPAREN); }
  {LSQUARE}                     { log("LSQUARE"); return symbol(sym.LSQUARE); }
  {RSQUARE}                     { log("RSQUARE"); return symbol(sym.RSQUARE); }
  {LBRACE}                      { log("LBRACE"); return symbol(sym.LBRACE); }
  {RBRACE}                      { log("RBRACE"); return symbol(sym.RBRACE); }
  {LBIND}                       { log("LBIND"); return symbol(sym.LBIND); }
  {RBIND}                       { log("RBIND"); return symbol(sym.RBIND); }
  {LDATA}                       { log("LDATA"); return symbol(sym.LDATA); }
  {RDATA}                       { log("RDATA"); return symbol(sym.RDATA); }

  /* Alphabetic keywords */
  "\\ELSE"                { log("ELSE"); return symbol(sym.ELSE); }
  "false"               { log("FALSE"); return symbol(sym.FALSE); }
  "function"            { log("FUNCTION"); return symbol(sym.FUNCTION); }
  "generic"             { log("GENERIC"); return symbol(sym.GENERIC); }
  "\\IF"                  { log("IF"); return symbol(sym.IF); }
  "leftassoc"           { log("LEFTASSOC"); return symbol(sym.LEFTASSOC); }
  "\\LET"                 { log("LET"); return symbol(sym.LET); }
  {POWER}               { log("POWER"); return symbol(sym.POWER); }
  "parents"             { log("PARENTS"); return symbol(sym.PARENTS); }
  "pre"                 { log("ZPRE"); return symbol(sym.ZPRE); }
  "relation"            { log("RELATION"); return symbol(sym.RELATION); }
  "rightassoc"          { log("RIGHTASSOC"); return symbol(sym.RIGHTASSOC); }
  "\\SECTION"             { log("SECTION"); return symbol(sym.SECTION); }
  "\\THEN"                { log("THEN"); return symbol(sym.THEN); }
  "true"                { log("TRUE"); return symbol(sym.TRUE); }

  /* Symbolic keywords */
  {COLON}               { log("COLON"); return symbol(sym.COLON); }
  "=="                  { log("DEFEQUAL"); return symbol(sym.DEFEQUAL); }
  {COMMA}               { log("COMMA"); return symbol(sym.COMMA); }
  "::="                 { log("DEFFREE"); return symbol(sym.DEFFREE); }
  "|"                   { log("BAR"); return symbol(sym.BAR); }
  "&"                   { log("ANDALSO"); return symbol(sym.ANDALSO); }
  {ZHIDE}               { log("ZHIDE"); return symbol(sym.ZHIDE); }
  "/"                   { log("SLASH"); return symbol(sym.SLASH); }
  {DOT}                 { log("DOT"); return symbol(sym.DOT); }
  {SEMICOLON}           { log("SEMICOLON"); return symbol(sym.SEMICOLON); }
  {LL}                  { log("ARG"); return symbol(sym.ARG); }
  ",,"                  { log("LISTARG"); return symbol(sym.LISTARG); }
  {EQUALS}              { log("EQUALS"); return symbol(sym.EQUALS); }
  {VDASH}   {INSTROKE}  { log("CONJECTURE"); return symbol(sym.CONJECTURE); }
  {ALL}                 { log("ALL"); return symbol(sym.ALL); }
  {SPOT}                { log("SPOT"); return symbol(sym.SPOT); }
  {EXI}                 { log("EXI"); return symbol(sym.EXI); }
  {EXI} {SE} "1" {NW}   { log("EXIONE"); return symbol(sym.EXIONE); }
  {IFF}                 { log("IFF"); return symbol(sym.IFF); }
  {IMP}                 { log("IMP"); return symbol(sym.IMP); }
  {OR}                  { log("OR"); return symbol(sym.OR); }
  {AND}                 { log("AND"); return symbol(sym.AND); }
  {NOT}                 { log("NOT"); return symbol(sym.NOT); }
  {MEM}                 { log("MEM"); return symbol(sym.MEM); }
  {ZPROJ}               { log("ZPROJ"); return symbol(sym.ZPROJ); }
  {CROSS}               { log("CROSS"); return symbol(sym.CROSS); }
  {LAMBDA}              { log("LAMBDA"); return symbol(sym.LAMBDA); }
  {MU}                  { log("MU"); return symbol(sym.MU); }
  {THETA}               { log("THETA"); return symbol(sym.THETA); }
  {ZCOMP}               { log("ZCOMP"); return symbol(sym.ZCOMP); }
  {ZPIPE}               { log("ZPIPE"); return symbol(sym.ZPIPE); }



  {HardSpace}           { log("SPACE"); }
  "\\\\"                { log("NL"); return symbol(sym.NL); }
  "\\also"              { log("NL"); return symbol(sym.NL); }
  "{"                   { }
  "}"                   { }
  {LineTerminator}                      { log("\n"); }

  {NUMERAL}          { 
                       log("NUMERAL(" + yytext() + ")");
                       return symbol(sym.NUMERAL, new Integer(yytext()));
                     }
  {DECORWORD}        {
                       log("DECORWORD(" + yytext() + ")");
                       return symbol(sym.DECORWORD, yytext());
                     }
  {STROKE}           {
                       log("STROKE(" + yytext() + ")");
                       return symbol(sym.STROKE, yytext());
                     }

  [^]                                   { log(yytext()); }
}

/* No token was found for the input so through an error.  Print out an
   Illegal character message with the illegal character that was found.
[^]                  { throw new Error("Illegal character <"+yytext()+">"); }
*/
