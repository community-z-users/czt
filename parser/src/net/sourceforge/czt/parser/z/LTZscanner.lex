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

%{
public OpMaps map;
private final int RELTYPE = 1;
private final int GENTYPE = 2;
private final int FUNTYPE = 3;
private int optype = 0;
private ArrayList list = new ArrayList();
%}

%init{
map = new OpMaps(); 

%init}

%state ZSECTION ZPARSER TEMPLATE

SLASH = [\\]
DIGIT = [0-9]
CHARACTER = [a-zA-Z]
GREEK = "\Xi"|"\Delta"|"\theta"|"\lambda"|"mu"
OTHERLETTER = "\arithmos"|"\nat"|"\nat_1"|"\num"|"\emptyset"
LETTER= (GREEK|CHARACTER|OTHERLETTER)
STROKECHAR=['!\?]
UNDERSCORE = "\_"
BRACKET = "("|")"|"["|"]"|"{"|"}"|"\lblot"|"\rblot"|"\ldata"|"\rdata"
SYMBOL = \||"&"|"\vdash"|"\land"|"\lor"|"\implies"|"\iff"|"\lnot"|"\forall"|"\exists"|"/"|"="|"\in"|"\mem"|":"|";"|","|"."|"@"|"\hide"|"\project"|"\semi"|"\pipe"|"+"|\|"\exists_1"
NUMERAL = ({DIGIT})+
STROKE = ({STROKECHAR}|("_"{DIGIT}))
WORD = ({NAME}({STROKE})*)
NAME = ({WORDPART})+|({LETTER}{ALPHASTR}({WORDPART})*)|({SYMBOL}{SYMBOLSTR}({WORDPART})*)
WORDPART = ({UNDERSCORE}({ALPHASTR}|{SYMBOLSTR}))
ALPHASTR = ({LETTER}|{DIGIT})*
SYMBOLSTR = ({SYMBOL})*
WHITE_SPACE_CHAR = [\n\ \t\r\b\012]
SPACE="~"|"\t1"|"\t2"|"\t3"|"\t4"|"\t5"|"\t6"|"\t7"|"\t8"|"\t9"|"\,"|"\:"|"\;"
NL = "\also"|\\\\
INFIXNAME = ({UNDERSCORE}({WORD})+{UNDERSCORE})
UNPARSED = {WORD}|{OTHERLETTER}|{STROKE}|{SLASH}
I ="\fun"|"\rel"|"\pfun"|"\pinj"|"\inj"|"\psurj"|"\surj"|"\bij"|"\ffun"|"\finj"|"\tfun"|"\tinj"|"\tsur"|"\psur"
POST="\inv"|"\star"|"\plus"|"\limg"|"rimg"|"\tcl"|"\rtcl"
PREP = "\disjoint"|"\#"
IP="\in"|"\notin"|"="|"\neq"|"\subseteq"|"\subset"|"\leq"|"\geq"|"\leqslant"|"geqslant"|"<"|">"|"\mem"|"\nmem"|"\psubs"|"\subs"|"\nem"
PRE="\tail"|"\head"|"\id"|"\seq"|"\iseq"|"\dom"|"\ran"|"\finset"|"\negate"|"\dcat"|"\bigcup"|"\bigcap"|"\fset"|"duni"|"dint"
%%

<YYINITIAL> "\begin{zsection}" {
	yybegin(ZSECTION);
	return new Symbol(LTZsym.BEGINZSECT, yytext());
	}
<YYINITIAL> "\begin{axdef}" {
	yybegin(ZPARSER);
	return new Symbol(LTZsym.BEGINAXDEF, yytext());
	}
<YYINITIAL> "\begin{schema}" {
	yybegin(ZPARSER);
	return new Symbol(LTZsym.BEGINSCHEMA, yytext());
	}
<YYINITIAL> "\begin{gendef}" {
	yybegin(ZPARSER);
	return new Symbol(LTZsym.BEGINGENDEF, yytext());
	}
<YYINITIAL>"\begin{genschema}" {
	yybegin(ZPARSER);
	return new  Symbol(LTZsym.BEGINSCHEMA, yytext());
	}
<YYINITIAL> "\begin{zed}" {
	yybegin(ZPARSER);
	return new Symbol(LTZsym.BEGINZED, yytext());
	}
<YYINITIAL> "\begin{zpar}" {return new Symbol(LTZsym.BEGINZPAR, yytext()); }
<YYINITIAL> "\end{zpar}" {return new Symbol(LTZsym.ENDZPAR, yytext()); }
<YYINITIAL> {UNPARSED} {return new Symbol(LTZsym.NARRPARA, yytext()); }
<YYINITIAL> {WHITE_SPACE_CHAR} { }
<YYINITIAL> {SPACE} { }
<YYINITIAL> . {return new Symbol(LTZsym.NARRPARA, yytext()); }

<ZSECTION> "\SECTION" {return new Symbol(LTZsym.SECTION, yytext()); }
<ZSECTION> "\parents" {return new Symbol(LTZsym.PARENTS, yytext()); }
<ZSECTION> "," {return new Symbol(LTZsym.COMMA, yytext()); }
<ZSECTION> "\end{zsection}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDZSECT, yytext());
	}
<ZSECTION> {WORD} {return new Symbol(LTZsym.WORD, yytext()); }
<ZSECTION> {WHITE_SPACE_CHAR} { }
<ZSECTION> {SPACE} { }
<ZSECTION> . {
    System.err.println("Unrecognizable by Lexer: @line"+yyline+";"+yytext());
	}


<ZPARSER> {PRE} {return new Symbol(LTZsym.PRETOK, yytext()); }
<ZPARSER> {IP} {return new Symbol(LTZsym.IPTOK, yytext()); }
<ZPARSER> {POST} {return new Symbol(LTZsym.POSTTOK, yytext()); }
<ZPARSER> {PREP} {return new Symbol(LTZsym.PREPTOK, yytext()); }
<ZPARSER> {I} {return new Symbol(LTZsym.ITOK, yytext()); }

<ZPARSER> "\power" {return new Symbol(LTZsym.POWER, "\\power"); }
<ZPARSER> "\pset" {return new Symbol(LTZsym.POWER, "\\power"); }

<ZPARSER> "\{" {return new Symbol(LTZsym.LSET, yytext()); }
<ZPARSER> "\}" {return new Symbol(LTZsym.RSET, yytext()); }
<ZPARSER> "\ldata" {return new Symbol(LTZsym.LDATA, "\\ldata"); }
<ZPARSER> "\lang" {return new Symbol(LTZsym.LDATA, "\\ldata"); }
<ZPARSER> "\rdata" {return new Symbol(LTZsym.RDATA, "\\rdata"); }
<ZPARSER> "\rang" {return new Symbol(LTZsym.RDATA, "\\rdata"); }
<ZPARSER> "\lblot" {return new Symbol(LTZsym.LBLOT, yytext()); }
<ZPARSER> "\rblot" {return new Symbol(LTZsym.RBLOT, yytext()); }

<ZPARSER> "\IF" {return new Symbol(LTZsym.IF, "\\IF"); }
<ZPARSER> "\THEN" {return new Symbol(LTZsym.THEN, "\\THEN"); }
<ZPARSER> "\ELSE" {return new Symbol(LTZsym.ELSE, "\\ELSE"); }
<ZPARSER> "\LET" {return new Symbol(LTZsym.LET, "\\LET"); }
<ZPARSER> "\true" {return new Symbol(LTZsym.TRUE, "true"); }
<ZPARSER> "\false" {return new Symbol(LTZsym.FALSE, "false"); }
<ZPARSER> "\pre" {return new Symbol(LTZsym.PRE, yytext()); }

<ZPARSER> ":" {return new Symbol(LTZsym.COLON, ":"); }
<ZPARSER> "==" {return new Symbol(LTZsym.HDEF, "=="); }
<ZPARSER> "\defs" {return new Symbol(LTZsym.HDEF, "=="); }
<ZPARSER> "," {return new Symbol(LTZsym.COMMA, ","); }
<ZPARSER> "\ddef" {return new Symbol(LTZsym.FREEEQ, "::="); }
<ZPARSER> "::=" {return new Symbol(LTZsym.FREEEQ, "::="); }
<ZPARSER> "|" {return new Symbol(LTZsym.BAR, "|"); }
<ZPARSER> "\cbar" {return new Symbol(LTZsym.BAR, "|"); }
<ZPARSER> "&" {return new Symbol(LTZsym.FREEAND, "&"); }
<ZPARSER> "\zhide" {return new Symbol(LTZsym.HIDE, "\\hide"); }
<ZPARSER> "\hide" {return new Symbol(LTZsym.HIDE, "\\hide"); }
<ZPARSER> "/" {return new Symbol(LTZsym.ANTISLASH, "/"); }
<ZPARSER> "." {return new Symbol(LTZsym.DOT, "."); }
<ZPARSER> ";" {return new Symbol(LTZsym.SEMI, ";"); }
<ZPARSER> {UNDERSCORE} {return new Symbol(LTZsym.UNDERSCORE, yytext()); }
<ZPARSER> "\vdash?" {return new Symbol(LTZsym.VDASH, yytext()); }
<ZPARSER> "\forall" {return new Symbol(LTZsym.FORALL, "\\forall"); }
<ZPARSER> "\all" {return new Symbol(LTZsym.FORALL, "\\forall"); }
<ZPARSER> "\spot" {return new Symbol(LTZsym.SPOT, "@"); }
<ZPARSER> "\dot" {return new Symbol(LTZsym.SPOT, "@"); }
<ZPARSER> "@" {return new Symbol(LTZsym.SPOT, "@"); }
<ZPARSER> "\exi" {return new Symbol(LTZsym.EXISTS, "\\exists"); }
<ZPARSER> "\exists" {return new Symbol(LTZsym.EXISTS, "\\exists"); }
<ZPARSER> "\exists_1" {return new Symbol(LTZsym.EXISTSONE, "\\exists_1"); }
<ZPARSER> "\exione" {return new Symbol(LTZsym.EXISTSONE, "\\exists_1"); }
<ZPARSER> "\iff" {return new Symbol(LTZsym.IFF, yytext()); }
<ZPARSER> "\imp" {return new Symbol(LTZsym.IMPLIES, "\\implies"); }
<ZPARSER> "\implies" {return new Symbol(LTZsym.IMPLIES, "\\implies"); }
<ZPARSER> "\lor" {return new Symbol(LTZsym.LOR, yytext()); }
<ZPARSER> "\land" {return new Symbol(LTZsym.LAND, yytext()); }
<ZPARSER> "\lnot" {return new Symbol(LTZsym.LNOT, yytext()); }
<ZPARSER> "\project" {return new Symbol(LTZsym.PROJECT, "\\project"); }
<ZPARSER> "\prod" {return new Symbol(LTZsym.CROSS, "\\cross"); }
<ZPARSER> "\cross" {return new Symbol(LTZsym.CROSS, "\\cross"); }
<ZPARSER> "\lambda" {return new Symbol(LTZsym.LAMBDA, yytext()); }
<ZPARSER> "\mu" {return new Symbol(LTZsym.MU, yytext()); }
<ZPARSER> "\theta" {return new Symbol(LTZsym.THETA, yytext()); }
<ZPARSER> "\zcmp" {return new Symbol(LTZsym.ZCOMP, "\\semi"); }
<ZPARSER> "\semi" {return new Symbol(LTZsym.ZCOMP, "\\semi"); }
<ZPARSER> "\zpipe" {return new Symbol(LTZsym.PIPE, "\\pipe"); }
<ZPARSER> "\pipe" {return new Symbol(LTZsym.PIPE, "\\pipe"); }
<ZPARSER> ",," {return new Symbol(LTZsym.OPERANDLIST, yytext()); }

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
	return new Symbol(LTZsym.ENDAXDEF, yytext());
	}
<ZPARSER> "\end{schema}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDSCHEMA, yytext());
	}
<ZPARSER> "\end{gendef}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDGENDEF, "\\end{gendef}");
	}
<ZPARSER> "\end{zed}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDZED, yytext());
	}
<ZPARSER> "\end{genschema}" {
	yybegin(YYINITIAL);
	return new Symbol(LTZsym.ENDSCHEMA, "\\end{schema}");
	}
<ZPARSER> "\infix{" {return new Symbol(LTZsym.UNDERINFIXREL, "\\infix{"); }
<ZPARSER> "{" {return new Symbol(LTZsym.LBRACE, "{"); }
<ZPARSER> "}" {return new Symbol(LTZsym.RBRACE, "}"); }
<ZPARSER> {SPACE} { }
<ZPARSER> {NL} {return new Symbol(LTZsym.NL, yytext()); }

<ZPARSER> "[" {return new Symbol(LTZsym.LSQUARE, "["); }
<ZPARSER> "]" {return new Symbol(LTZsym.RSQUARE, "]"); }

<ZPARSER> "\sdef" {return new Symbol(LTZsym.HDEF, "=="); }
<ZPARSER> "(" {return new Symbol(LTZsym.LBRACKET, "("); }
<ZPARSER> ")" {return new Symbol(LTZsym.RBRACKET, ")"); }

<ZPARSER> "+" {return new Symbol(LTZsym.PLUS, "+"); }
<ZPARSER> "-" {return new Symbol(LTZsym.MINUS, "-"); }
<ZPARSER> "*" {return new Symbol(LTZsym.TIMES, "*"); }
<ZPARSER> "\div" {return new Symbol(LTZsym.DIV, "\\div"); }
<ZPARSER> "\mod" {return new Symbol(LTZsym.MOD, "\\mod"); }

<ZPARSER> "\zrelation" {
       optype = RELTYPE;
	yybegin(TEMPLATE);
	return new Symbol(LTZsym.ZRELATION, "\\relationi");
	}
<ZPARSER> "\relation" {
       optype = RELTYPE;
	yybegin(TEMPLATE);
	return new Symbol(LTZsym.ZRELATION, yytext());
	}
<ZPARSER> "\zfunction" {
        optype = FUNTYPE;
	yybegin(TEMPLATE);
	return new Symbol(LTZsym.ZFUNCTION, "\\function");
	}
<ZPARSER> "\function" {
        optype = FUNTYPE;
	yybegin(TEMPLATE);
	return new Symbol(LTZsym.ZFUNCTION, yytext());
	}
<ZPARSER> "\zgeneric" {
        optype = GENTYPE;
	yybegin(TEMPLATE);
	return new Symbol(LTZsym.ZGENERIC, "\\generic");
	}
<ZPARSER> "\generic" {
        optype = GENTYPE;
	yybegin(TEMPLATE);
	return new Symbol(LTZsym.ZGENERIC, yytext());
	}

<ZPARSER> {STROKE} {return new Symbol(LTZsym.STROKE, yytext()); }
<ZPARSER> {DIGIT}+ {return new Symbol(LTZsym.DIGIT, yytext()); }
<ZPARSER> {WORD} {return new Symbol(LTZsym.WORD, yytext()); }
<ZPARSER> {OTHERLETTER} {return new Symbol(LTZsym.WORD, yytext()); }

<ZPARSER> {WHITE_SPACE_CHAR} { }
<ZPARSER> . {
    System.err.println("Unrecognizable by Lexer: @line"+yyline+";"+yytext());
}

<TEMPLATE> "\leftassoc" {return new Symbol(LTZsym.ASSOC, "Left"); }
<TEMPLATE> "\rightassoc" {return new Symbol(LTZsym.ASSOC, "Right"); }
<TEMPLATE> {UNDERSCORE} {
        Symbol val = new Symbol(LTZsym.UNDERSCORE, yytext());
	list.add(val);
	return val; }
<TEMPLATE> "(" {return new Symbol(LTZsym.LBRACKET, "("); }
<TEMPLATE> ")" {
        int listsize = list.size();
	if(listsize == 2){ //if layer 1
               Symbol firstinsym = (Symbol)list.get(0);
               ArrayList resultlist = new ArrayList();
	       if(firstinsym.sym == LTZsym.UNDERSCORE){ //if layer 2
		   //-           s               null            null            => "posttok" or "postptok"             
		   if(optype == RELTYPE){ //if layer 3
			 resultlist.add("postptok");
			 resultlist.add("relation");
	            } //end if layer 3
		    else{ //else layer 3
			 resultlist.add("posttok");
			 if(optype == FUNTYPE) 
			     resultlist.add("function");
			 else resultlist.add("generic");
		     } //end else layer 3
		     map.addOp((String)((Symbol)list.get(1)).value, resultlist);
		 } //end if layer 2
		 else{ //else layer2
                      // null       s               null             -               => "pretop" or "preptok"		     
		      if(optype == RELTYPE){ //if layer 3
		          resultlist.add("preptok"); 
			  resultlist.add("relation");
		      } //end if layer 3
		      else{ //else layer 3
		           resultlist.add("pretop");
			   if(optype == FUNTYPE)  resultlist.add("function");
			   else resultlist.add("generic");
		      } //end else layer 3
		      map.addOp((String)firstinsym.value, resultlist);
		   } //end else layer 2
            }//end list size = 2 and end if layer 1
            else if(listsize == 3){ //if layer 1
	          Symbol firstinsym = (Symbol)list.get(0);
		  if(firstinsym.sym == LTZsym.UNDERSCORE){ //if layer 2
		      //-           s               null             -               => "itok" or "iptok"
		      Symbol operand = (Symbol)list.get(1);
            	      ArrayList resultlist = new ArrayList();
		      if(optype == RELTYPE){
		         resultlist.add("itok");
			 resultlist.add("relation");
	               }
		       else{
		          resultlist.add("iptok");
			  if(optype == FUNTYPE) resultlist.add("function");
			  else resultlist.add("generic");
			}
			map.addOp((String)operand.value, resultlist);
		   } // end if layer 2
		   else{ //else layer 2
		        //null  s size = 2  null    => "ltok (ertok | srtok) " or "lptok (erptok | srptok)"
			if(optype == RELTYPE){ //if layer 3
			    Symbol tempSym = (Symbol)list.get(0);
			    ArrayList resultlist = new ArrayList();
			    resultlist.add("lptok");
			    resultlist.add("relation");
			    map.addOp((String)tempSym.value, resultlist);
			    resultlist.clear();
			    tempSym = (Symbol)list.get(1);
			    if(tempSym.sym == LTZsym.UNDERSCORE){ //if layer 4
			       tempSym = (Symbol)list.get(2);
			       resultlist.add("erptok");
			       if(optype == FUNTYPE) resultlist.add("function");
       			       else resultlist.add("generic");
			       map.addOp((String)tempSym.value, resultlist);
			    } //end if layer 4
			    else{ //else layer 4
		               tempSym = (Symbol)list.get(2);
			       resultlist.add("srptok");
			       if(optype == FUNTYPE) resultlist.add("function");
       			       else resultlist.add("generic");
			       map.addOp((String)tempSym.value, resultlist);
			    } //end else layer 4
			 }//end outer if layer 3
                         else{ //else layer 3
			    Symbol tempSym = (Symbol)list.get(0);
			    ArrayList resultlist = new ArrayList();
			    resultlist.add("ltok");
			    resultlist.add("relation");
			    map.addOp((String)tempSym.value, resultlist);
			    resultlist.clear();
			    tempSym = (Symbol)list.get(1);
			    if(tempSym.sym == LTZsym.UNDERSCORE){ //if layer 4
			       tempSym = (Symbol)list.get(2);
			       resultlist.add("ertok");
			       if(optype == FUNTYPE) resultlist.add("function");
       			       else resultlist.add("generic");
			       map.addOp((String)tempSym.value, resultlist);
			    } //end if layer 4
			    else{ //else layer 4
		               tempSym = (Symbol)list.get(2);
			       resultlist.add("srtok");
			       if(optype == FUNTYPE) resultlist.add("function");
       			       else resultlist.add("generic");
			       map.addOp((String)tempSym.value, resultlist);
			    } //end else layer 4
			 } //end else layer 3
		   }//end outer else layer 2
	     }//end list size = 3 and end if 1
	     else if (listsize == 4){ //if layer 1
/*  
-           s           size = 2          null            => "eltok (ertok|srtok) " or "elptok (eretok | sretok)"
 null       s           size = 2           -               => "ltok (eretok | sretok)" or "lptok (ereptok | sreptok)"
 */          }
              else if (listsize == 5){
// -           s           size = 2           -               => "eltok (eretok|sretok)" or "elptok (ereptok | sreptok)"
              }
	      else{
	      }
	yybegin(ZPARSER);
	return new Symbol(LTZsym.RBRACKET, ")");
	}
<TEMPLATE> ",," {
        Symbol val = new Symbol(LTZsym.OPERANDLIST, yytext());
	list.add(val);
	return val;  }
<TEMPLATE> {DIGIT}+ { return new Symbol(LTZsym.PREC, yytext()); }
<TEMPLATE> {WORD} {
         Symbol val = new Symbol(LTZsym.WORD, yytext());
	 list.add(val);
	 return val; }
<TEMPLATE> {WHITE_SPACE_CHAR} { }
<TEMPLATE> {SPACE} { }
<TEMPLATE> . {
	System.err.println("Unrecognizable symbol in template: @line " + yyline + " ; " + yytext());
	}


