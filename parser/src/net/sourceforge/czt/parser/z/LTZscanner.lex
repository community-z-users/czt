package net.sourceforge.czt.parser.z;

import java.lang.*;
import java.util.*;
import java_cup.runtime.*;
import net.sourceforge.czt.parser.z.ast.*;

%%

%cup
%class LTZscanner
%line
%type Symbol

%eofval{
	return (new Symbol(LTZsym.EOF, null));
%eofval}

%state ZSECTION ZPARSER TEMPLATE

SLASH = [\\]
NUMBER = [0-9]
STROKECHAR=['!\?]
STROKE = ({STROKECHAR}|("_"{NUMBER}))
SPECIALLETTER = "\arithmos"|"\nat"|"\nat_1"|"\num"|"\emptyset"|"\emptyseq"|"\max"|"\min"
UNDERSCORE = "\_"
CHARACTER = [a-zA-Z]
GREEK = "\Xi"|"\Delta"
NAME = (({CHARACTER}|{NUMBER})+{WORDPART}*{NUMBER}*)
WORD = ({NAME}{STROKE}?)
WORDPART = ({UNDERSCORE}{CHARACTER}+)
INFIXNAME = ({UNDERSCORE}({WORD})+{UNDERSCORE})
UNPARSED = {WORD}|{SPECIALLETTER}|{STROKE}|{SLASH}
WHITE_SPACE_CHAR = [\n\ \t\r\b\012]
SPACE="~"|"\t1"|"\t2"|"\t3"|"\t4"|"\t5"|"\t6"|"\t7"|"\t8"|"\t9"|"\,"|"\:"|"\;"
INFIXGENERIC="\fun"|"\rel"|"\pfun"|"\pinj"|"\inj"|"\psurj"|"\surj"|"\bij"|"\ffun"|"\finj"|"\tfun"|"\tinj"|"\tsur"|"\psur"
POSTFIXFUN="\inv"|"\star"|"\plus"|"\limg"|"rimg"|"\tcl"|"\rtcl"
PREFIXFUN = "\#"
PREFIXREL = "\disjoint"
INFIXREL="\in"|"\notin"|"="|"\neq"|"\subseteq"|"\subset"|"\leq"|"\geq"|"\leqslant"|"geqslant"|"<"|">"|"\mem"|"\nmem"|"\psubs"|"\subs"|"\nem"
PREGENERIC="\tail"|"\head"|"\id"|"\seq"|"\iseq"|"\dom"|"\ran"|"\finset"|"\negate"|"\dcat"|"\bigcup"|"\bigcap"|"\fset"|"duni"|"dint"
%%

<YYINITIAL> "\begin{zsection}" {
	yybegin(ZSECTION);
	return new Symbol(LTZsym.BEGINZSECT, "\\begin{zsection}");
	}
<YYINITIAL> "\begin{axdef}" {
	yybegin(ZPARSER);
	return new Symbol(LTZsym.BEGINAXDEF, "\\begin{axdef}");
	}
<YYINITIAL> "\begin{schema}" {
	yybegin(ZPARSER);
	return new Symbol(LTZsym.BEGINSCHEMA, "\\begin{schema}");
	}
<YYINITIAL> "\begin{gendef}" {
	yybegin(ZPARSER);
	return new Symbol(LTZsym.BEGINGENDEF, "\\begin{gendef}");
	}
<YYINITIAL>"\begin{genschema}" {
	yybegin(ZPARSER);
	return new  Symbol(LTZsym.BEGINGENSCHEMA, "\\begin{genschema}");
	}
<YYINITIAL> "\begin{zed}" {
	yybegin(ZPARSER);
	return new Symbol(LTZsym.BEGINZED, "\\begin{zed}");
	}
<YYINITIAL> "\begin{zpar}" {return new Symbol(LTZsym.BEGINZPAR, "\\begin{zpar}"); }
<YYINITIAL> "\end{zpar}" {return new Symbol(LTZsym.ENDZPAR, "\\end{zpar}"); }
<YYINITIAL> {UNPARSED} {return new Symbol(LTZsym.NARRPARA, yytext()); }
<YYINITIAL> {WHITE_SPACE_CHAR} { }
<YYINITIAL> {SPACE} { }
<YYINITIAL> . {return new Symbol(LTZsym.NARRPARA, yytext()); }

<ZSECTION> "\SECTION" {return new Symbol(LTZsym.SECTION, "\\SECTION"); }
<ZSECTION> "\parents" {return new Symbol(LTZsym.PARENTS, "\\parents"); }
<ZSECTION> "," {return new Symbol(LTZsym.COMMA, ","); }
<ZSECTION> "\end{zsection}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDZSECT, "\\end{zsection}");
	}
<ZSECTION> {WORD} {return new Symbol(LTZsym.WORD, yytext()); }
<ZSECTION> {WHITE_SPACE_CHAR} { }
<ZSECTION> {SPACE} { }
<ZSECTION> . {
    System.err.println("Unrecognizable by Lexer: @line"+yyline+";"+yytext());
	}

<ZPARSER> {GREEK} {return new Symbol(LTZsym.GREEK, yytext()); }
<ZPARSER> "\theta" {return new Symbol(LTZsym.THETA, "\\theta"); }
<ZPARSER> "\lambda" {return new Symbol(LTZsym.LAMBDA, "\\lambda"); }
<ZPARSER> "\mu" {return new Symbol(LTZsym.MU, "\\mu"); }
<ZPARSER> "\power" {return new Symbol(LTZsym.POWER, "\\power"); }
<ZPARSER> "\pset" {return new Symbol(LTZsym.POWER, "\\power"); }
<ZPARSER> {UNDERSCORE} {return new Symbol(LTZsym.UNDERSCORE, "\\_"); }
<ZPARSER> "\{" {return new Symbol(LTZsym.LSET, "\\{"); }
<ZPARSER> "\}" {return new Symbol(LTZsym.RSET, "\\}"); }
<ZPARSER> "\ldata" {return new Symbol(LTZsym.LDATA, "\\ldata"); }
<ZPARSER> "\lang" {return new Symbol(LTZsym.LDATA, "\\ldata"); }
<ZPARSER> "\rdata" {return new Symbol(LTZsym.RDATA, "\\rdata"); }
<ZPARSER> "\rang" {return new Symbol(LTZsym.RDATA, "\\rdata"); }
<ZPARSER> "\lblot" {return new Symbol(LTZsym.LBLOT, "\\lblot"); }
<ZPARSER> "\rblot" {return new Symbol(LTZsym.RBLOT, "\\rblot"); }

<ZPARSER> "\vdash?" {return new Symbol(LTZsym.VDASH, "\\vdash"); }
<ZPARSER> "\land" {return new Symbol(LTZsym.LAND, "\\land"); }
<ZPARSER> "\lor" {return new Symbol(LTZsym.LOR, "\\lor"); }
<ZPARSER> "\imp" {return new Symbol(LTZsym.IMPLIES, "\\implies"); }
<ZPARSER> "\implies" {return new Symbol(LTZsym.IMPLIES, "\\implies"); }
<ZPARSER> "\iff" {return new Symbol(LTZsym.IFF, "\\iff"); }
<ZPARSER> "\lnot" {return new Symbol(LTZsym.LNOT, "\\lnot"); }
<ZPARSER> "\forall" {return new Symbol(LTZsym.FORALL, "\\forall"); }
<ZPARSER> "\all" {return new Symbol(LTZsym.FORALL, "\\all"); }
<ZPARSER> "\exi" {return new Symbol(LTZsym.EXISTS, "\\exists"); }
<ZPARSER> "\exists" {return new Symbol(LTZsym.EXISTS, "\\exists"); }
<ZPARSER> "\prod" {return new Symbol(LTZsym.CROSS, "\\cross"); }
<ZPARSER> "\cross" {return new Symbol(LTZsym.CROSS, "\\cross"); }
<ZPARSER> "\spot" {return new Symbol(LTZsym.SPOT, "@"); }
<ZPARSER> "\dot" {return new Symbol(LTZsym.SPOT, "@"); }
<ZPARSER> "@" {return new Symbol(LTZsym.SPOT, "@"); }
<ZPARSER> "\zhide" {return new Symbol(LTZsym.HIDE, "\\hide"); }
<ZPARSER> "\hide" {return new Symbol(LTZsym.HIDE, "\\hide"); }
<ZPARSER> "\project" {return new Symbol(LTZsym.PROJECT, "\\project"); }
<ZPARSER> "\zcmp" {return new Symbol(LTZsym.ZCOMP, "\\semi"); }
<ZPARSER> "\semi" {return new Symbol(LTZsym.ZCOMP, "\\semi"); }
<ZPARSER> "\zpipe" {return new Symbol(LTZsym.PIPE, "\\pipe"); }
<ZPARSER> "\pipe" {return new Symbol(LTZsym.PIPE, "\\pipe"); }

<ZPARSER> "\IF" {return new Symbol(LTZsym.IF, "\\IF"); }
<ZPARSER> "\THEN" {return new Symbol(LTZsym.THEN, "\\THEN"); }
<ZPARSER> "\ELSE" {return new Symbol(LTZsym.ELSE, "\\ELSE"); }
<ZPARSER> "\LET" {return new Symbol(LTZsym.LET, "\\LET"); }
<ZPARSER> "\uni" {return new Symbol(LTZsym.CUP, "\\cup"); }
<ZPARSER> "\union" {return new Symbol(LTZsym.CUP, "\\cup"); }
<ZPARSER> "\cup" {return new Symbol(LTZsym.CUP, "\\cup"); }
<ZPARSER> "\int" {return new Symbol(LTZsym.CAP, "\\cap"); }
<ZPARSER> "\cap" {return new Symbol(LTZsym.CAP, "\\cap"); }
<ZPARSER> "\setminus" {return new Symbol(LTZsym.SETMINUS, "\\setminus"); }
<ZPARSER> "\symdiff" {return new Symbol(LTZsym.SYMDIFF, "\\symdiff"); }
<ZPARSER> "\mapsto" {return new Symbol(LTZsym.MAPSTO, "\\mapsto"); }
<ZPARSER> "\fcmp" {return new Symbol(LTZsym.COMP, "\\comp"); }
<ZPARSER> "\comp" {return new Symbol(LTZsym.COMP, "\\comp"); }
<ZPARSER> "\circ" {return new Symbol(LTZsym.CIRC, "\\circ"); }
<ZPARSER> "\dres" {return new Symbol(LTZsym.DRES, "\\dres"); }
<ZPARSER> "\rres" {return new Symbol(LTZsym.RRES, "\\rres"); }
<ZPARSER> "\dsub" {return new Symbol(LTZsym.NDRES, "\\ndres"); }
<ZPARSER> "\ndres" {return new Symbol(LTZsym.NDRES, "\\ndres"); }
<ZPARSER> "\rsub" {return new Symbol(LTZsym.NRRES, "\\nrres"); }
<ZPARSER> "\nrres" {return new Symbol(LTZsym.NRRES, "\\nrres"); }
<ZPARSER> "\oplus" {return new Symbol(LTZsym.OPLUS, "\\oplus"); }
<ZPARSER> "\fovr" {return new Symbol(LTZsym.OPLUS, "\\oplus"); }
<ZPARSER> "\upto" {return new Symbol(LTZsym.UPTO, "\\upto"); }
<ZPARSER> "\lseq" {return new Symbol(LTZsym.LANGLE,  "\\langle"); }
<ZPARSER> "\langle" {return new Symbol(LTZsym.LANGLE, "\\langle"); }
<ZPARSER> "\rseq" {return new Symbol(LTZsym.RANGLE, "\\rangle"); }
<ZPARSER> "\rangle" {return new Symbol(LTZsym.RANGLE, "\\rangle"); }
<ZPARSER> "\cat" {return new Symbol(LTZsym.CAT, "\\cat"); }
<ZPARSER> "\ires" {return new Symbol(LTZsym.EXTRACT, "\\extract"); }
<ZPARSER> "\extract" {return new Symbol(LTZsym.EXTRACT, "\\extract"); }
<ZPARSER> "\sres" {return new Symbol(LTZsym.FILTER, "\\filter"); }
<ZPARSER> "\filter" {return new Symbol(LTZsym.FILTER, "\\filter"); }

<ZPARSER> "\where" {return new Symbol(LTZsym.WHERE, "\\where"); }
<ZPARSER> "\ST" {return new Symbol(LTZsym.WHERE, "\\where"); }
<ZPARSER> "\end{axdef}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDAXDEF, "\\end{axdef}");
	}

<ZPARSER> "\end{schema}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDSCHEMA, "\\end{schema}");
	}

<ZPARSER> "\end{gendef}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDGENDEF, "\\end{gendef}");
	}

<ZPARSER> "\end{zed}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDZED, "\\end{zed}");
	}
<ZPARSER> "\end{genschema}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDGENSCHEMA, "\\end{genschema}");
	}

<ZPARSER> "\infix{" {return new Symbol(LTZsym.UNDERINFIXREL, "\\infix{"); }
<ZPARSER> "{" {return new Symbol(LTZsym.LBRACE, "{"); }
<ZPARSER> "}" {return new Symbol(LTZsym.RBRACE, "}"); }
<ZPARSER> {SPACE} { }
<ZPARSER> {SLASH}{SLASH} {return new Symbol(LTZsym.NL, new String("\\" + "\\")); }
<ZPARSER> "\also" {return new Symbol(LTZsym.NL, new String("\\" + "\\")); }

<ZPARSER> "[" {return new Symbol(LTZsym.LSQUARE, "["); }
<ZPARSER> "]" {return new Symbol(LTZsym.RSQUARE, "]"); }
<ZPARSER> ";" {return new Symbol(LTZsym.SEMI, ";"); }
<ZPARSER> "," {return new Symbol(LTZsym.COMMA, ","); }
<ZPARSER> "&" {return new Symbol(LTZsym.FREEAND, "&"); }
<ZPARSER> "==" {return new Symbol(LTZsym.HDEF, "=="); }
<ZPARSER> "\defs" {return new Symbol(LTZsym.HDEF, "=="); }
<ZPARSER> "\sdef" {return new Symbol(LTZsym.SDEF, "\\sdef"); }
<ZPARSER> "\ddef" {return new Symbol(LTZsym.FREEEQ, "::="); }
<ZPARSER> "::=" {return new Symbol(LTZsym.FREEEQ, "::="); }
<ZPARSER> "|" {return new Symbol(LTZsym.BAR, "|"); }
<ZPARSER> "\cbar" {return new Symbol(LTZsym.BAR, "|"); }
<ZPARSER> "\exists_1" {return new Symbol(LTZsym.EXISTSONE, "\\exists_1"); }
<ZPARSER> "\exione" {return new Symbol(LTZsym.EXISTSONE, "\\exists_1"); }
<ZPARSER> "true" {return new Symbol(LTZsym.TRUE, "true"); }
<ZPARSER> "false" {return new Symbol(LTZsym.FALSE, "false"); }
<ZPARSER> "(" {return new Symbol(LTZsym.LBRACKET, "("); }
<ZPARSER> ")" {return new Symbol(LTZsym.RBRACKET, ")"); }
<ZPARSER> "\pre" {return new Symbol(LTZsym.PRE, "\\pre"); }
<ZPARSER> "." {return new Symbol(LTZsym.DOT, "."); }

<ZPARSER> "/" {return new Symbol(LTZsym.ANTISLASH, "/"); }
<ZPARSER> ":" {return new Symbol(LTZsym.COLON, ":"); }
<ZPARSER> "+" {return new Symbol(LTZsym.PLUS, "+"); }
<ZPARSER> "-" {return new Symbol(LTZsym.MINUS, "-"); }
<ZPARSER> "*" {return new Symbol(LTZsym.TIMES, "*"); }
<ZPARSER> "\div" {return new Symbol(LTZsym.DIV, "\\div"); }
<ZPARSER> "\mod" {return new Symbol(LTZsym.MOD, "\\mod"); }

<ZPARSER> "\zrelation" {
	yybegin(TEMPLATE);
	return new Symbol(LTZsym.ZRELATION, yytext());
	}
<ZPARSER> "\zfunction" {
	yybegin(TEMPLATE);
	return new Symbol(LTZsym.ZFUNCTION, yytext());
	}
<ZPARSER> "\zgeneric" {
	yybegin(TEMPLATE);
	return new Symbol(LTZsym.ZGENERIC, yytext());
	}
<ZPARSER> {PREGENERIC} {return new Symbol(LTZsym.PREGENERIC, yytext()); }
<ZPARSER> {PREFIXFUN} {return new Symbol(LTZsym.PREFIXFUN, yytext()); }
<ZPARSER> {INFIXREL} {return new Symbol(LTZsym.INFIXREL, yytext()); }
<ZPARSER> {POSTFIXFUN} {return new Symbol(LTZsym.POSTFIXFUN, yytext()); }
<ZPARSER> {PREFIXREL} {return new Symbol(LTZsym.PREFIXREL, yytext()); }
<ZPARSER> {INFIXGENERIC} {return new Symbol(LTZsym.INFIXGENERIC, yytext()); }
<ZPARSER> {STROKE} {return new Symbol(LTZsym.STROKE, yytext()); }
<ZPARSER> {WORD} {return new Symbol(LTZsym.WORD, yytext()); }
<ZPARSER> {SPECIALLETTER} {return new Symbol(LTZsym.WORD, yytext()); }
<ZPARSER> {NUMBER}+ {return new Symbol(LTZsym.NUMBER, yytext()); }

<ZPARSER> {WHITE_SPACE_CHAR} { }

<ZPARSER> . {
    System.err.println("Unrecognizable by Lexer: @line"+yyline+";"+yytext());
}

<TEMPLATE> "\leftassoc" {return new Symbol(LTZsym.ASSOC, "Left"); }
<TEMPLATE> "\rightassoc" {return new Symbol(LTZsym.ASSOC, "Right"); }
<TEMPLATE> {UNDERSCORE} {return new Symbol(LTZsym.UNDERSCORE, yytext()); }
<TEMPLATE> "(" {return new Symbol(LTZsym.LBRACKET, "("); }
<TEMPLATE> ")" {
	yybegin(ZPARSER);
	return new Symbol(LTZsym.RBRACKET, ")");
	}
<TEMPLATE> "\power" {return new Symbol(LTZsym.POWER, "\\power"); }
<TEMPLATE> ",," {return new Symbol(LTZsym.OPERANDLIST, ",,"); }
<TEMPLATE> {NUMBER}+ { return new Symbol(LTZsym.PREC, yytext()); }
<TEMPLATE> {WORD} {return new Symbol(LTZsym.WORD, yytext()); }
<TEMPLATE> {WHITE_SPACE_CHAR} { }
<TEMPLATE> {SPACE} { }
<TEMPLATE> . {
	System.err.println("Unrecognizable symbol in template: @line " + yyline + " ; " + yytext());
	}

