/* --------------------------Usercode Section------------------------ */
package net.sourceforge.czt.scanner;

import java.io.*;
import java.util.*;

import java_cup.runtime.*;

import net.sourceforge.czt.util.ZChar;      
%%
   
/* -----------------Options and Declarations Section----------------- */

%class Latex2Unicode
%unicode
%line
%column
%standalone
%eof{
  try {
    writer_.close();
  } catch (Exception e) {
    System.err.println("Cannot close writer " + writer_);
    e.printStackTrace();
  }
%eof}

%{
  Writer writer_ = createWriter();

  private Writer createWriter()
  {
    try {
      return new OutputStreamWriter(new FileOutputStream("out.utf8"), "utf8");
    } catch (Exception e) {
      System.err.println("Cannot open file out.utf8");
      e.printStackTrace();
      return null;
    }
  }

  public void setWriter(Writer writer)
  {
    writer_ = writer;
  }

  private void latexCommand(String command, boolean spaces)
    throws IOException
  {
    String zstring = LatexMarkup.toUnicode(command, spaces);
    if (zstring != null) {
      print(zstring);
    } else {
      print(command);
    }
  }

  private void print(char character)
    throws IOException
  {
    print(String.valueOf(character));
  }

  private void print(String message)
    throws IOException
  {
    writer_.write(message);
  }
%}

WS = [\n\r\ \t\b\012]
HS = "~" | "\\," | "\\:" | "\\;" | "\\ "
  | "\\tl" | "\\t2" | "\\t3" | "\\t4" | "\\t5" | "\\t6" | "\\t7" | "\\t8" | "\\t9"

ALPHA = [a-zA-Z]
NOT_ALPHA = !(![^] | {ALPHA})

%state ZED

%%
/* ------------------------Lexical Rules Section---------------------- */

<YYINITIAL> {
  "\\begin{axdef}"                      {
                                          yybegin(ZED);
                                          print(ZChar.AXCHAR);
                                        }
  "\\begin{gendef}"                     {
                                          yybegin(ZED);
                                          print(ZChar.AXCHAR);
                                          print(ZChar.GENCHAR);
                                        }
  "\\begin{schema}"                     {
                                          yybegin(ZED);
                                          print(ZChar.SCHCHAR);
                                        }
  "\\begin{zed}" /* not in standard? */ {
                                          yybegin(ZED);
                                          print(ZChar.ZEDCHAR);
                                        }
  "\\begin{zsection}"                   {
                                          yybegin(ZED);
                                          print(ZChar.ZEDCHAR);
                                        }
  [^]                                   {
                                          print(yytext());
                                        }
}

<ZED> {
  /* TODO LaTex comment */
  {WS}                                  { }
  {HS}                                  { print(" "); }
  "\\\\" | "\\also" | "\\znewpage"      { print("\n"); }
  "\\end{axdef}"                        { yybegin(YYINITIAL);
                                          print(ZChar.ENDCHAR); }
  "\\end{gendef}"                       { yybegin(YYINITIAL);
                                          print(ZChar.ENDCHAR); }
  "\\end{schema}"                       { yybegin(YYINITIAL);
                                          print(ZChar.ENDCHAR); }
  "\\end{zed}" /* not in standard? */   { yybegin(YYINITIAL);
                                          print(ZChar.ENDCHAR); }
  "\\end{zsection}"                     { yybegin(YYINITIAL);
                                          print(ZChar.ENDCHAR); }
  "\\where"                             { print(" ");
                                          print(ZChar.VL);
                                          print(" ");
                                        }
  "\\" . | "\\" {ALPHA}*                { latexCommand(yytext(), true);}
  "{\\" . "}" | "{\\" {ALPHA}* "}" 
         { latexCommand(yytext().substring(1, yytext().length() - 1), false); }
  "{" | "}"                             { }
  .                                     { print(yytext()); }
}
