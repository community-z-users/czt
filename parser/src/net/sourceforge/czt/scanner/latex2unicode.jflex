/* --------------------------Usercode Section------------------------ */
package net.sourceforge.czt.scanner;

import java.io.*;
import java.util.*;

import java_cup.runtime.*;

import net.sourceforge.czt.util.ZString;
%%

/* -----------------Options and Declarations Section----------------- */

%class Latex2Unicode
%public
%unicode
%line
%column
%cup
%eof{
  try {
    if (writer_ != null) writer_.close();
  } catch (Exception e) {
    System.err.println("Cannot close writer " + writer_);
    e.printStackTrace();
  }
%eof}

%{
  /**
   * The writer where the output goes in.
   */
  Writer writer_;

  /**
   * Lexes a given file.
   */
  public static void main(String[] args) {    
    String usage = "Usage: java net.sourceforge.czt.scanner.Latex2Unicode"
      + " [ -in <inputfile>] [ -out <outputfile>]";
    try {
      InputStream input = System.in;
      Writer writer = new PrintWriter(System.out);
      for (int i = 0; i < args.length; i++) {
        if ("-in".equals(args[i])) {
          if (i < args.length) {
            input = new FileInputStream(args[++i]);
          } else {
            System.err.println(usage);
            return;
          }
        } else if ("-out".equals(args[i])) {
          if (i < args.length) {
            writer =
              new OutputStreamWriter(new FileOutputStream(args[++i]), "utf8");
          } else {
            System.err.println(usage);
            return;
          }
        } else {
          System.err.println(usage);
          return;
        }
      }
      Latex2Unicode lexer = new Latex2Unicode(input);
      lexer.setWriter(writer);
      Symbol s = null;
      while ( (s = lexer.next_token()).sym != sym.EOF) {
        writer.write((String) s.value);
      }
      writer.close();
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

  /**
   * A stack of BraceType.
   * Each "{"-token pushs a BraceType on the stack,
   * each "}"-token pops a BraceType from the stack.
   *
   * A "^"-token followed by "{"-token pushs
   * a <code>BraceType.SUPER</code> (no space to be inserted after the scripts)
   * or <code>BraceType.SUPER_SPACE</code> (space has to be inserted after
   * the scripts) on the stack.  A "_"-token followed by "{"-token pushs
   * a <code>BraceType.SUB</code> (no space to be inserted after the scripts)
   * or <code>BraceType.SUB_SPACE</code> (space has to be inserted after
   * the scripts) on the stack.  All other "{"-token just push a
   * <code>BraceType.BRACE</code> on the stack.
   */
  Stack braceStack_ = new Stack();

  /**
   * A boolean indicating whether a space has to inserted after all
   * following subscripts and superscripts.
   */
  boolean addSpace_ = false;

  /**
   * A flag telling whether the next "}" is tranlated into space or not.
   * This is used when a /begin{schema} is found. This is followed by
   * {NAME} and the "}" should be translated into space.
   */
  boolean braceToSpace_ = false;

  /**
   * Sets the given writer as output used by this transformer.
   */
  public void setWriter(Writer writer)
  {
    writer_ = writer;
  }

  /**
   * Prints the given message to the output stream.
   */
  private Symbol result(String message)
    throws IOException
  {
    return new Symbol(2, yyline, yycolumn, message);
  }

  /**
   * Writes a space to the output and sets
   * <code>addSpace_</code> to <code>false</code>
   * if <code>addSpace_</code> is <code>true</code>.
   * Does nothing if <code>addSpace_</code> is
   * <code>false</code>.
   */
  private String addSpace()
    throws IOException
  {
    if (addSpace_) {
      addSpace_ = false;
      return ZString.SPACE;
    }
    return "";
  }

  /**
   * Returns a north east arrow if <code>string</code>
   * equals "^" and a south east arrow if
   * <code>string</code> equalas "_".
   * Throws an IllegalArgumentException for all other strings.
   */
  private String beginScript(String string)
  {
    if ("^".equals(string)) return ZString.NE;
    if ("_".equals(string)) return ZString.SE;
    throw new IllegalArgumentException();
  }

  /**
   * Returns a south west arrow if <code>string</code>
   * equals "^" and a north west arrow if
   * <code>string</code> equalas "_".
   * Throws an IllegalArgumentException for all other strings.
   */
  private String endScript(String string)
  {
    if ("^".equals(string)) return ZString.SW;
    if ("_".equals(string)) return ZString.NW;
    throw new IllegalArgumentException();
  }

  /**
   * Throws an exception if the <code>assertion</code> is false.
   * This method is used instead of <code>assert Expression;</code>
   * since this cannot be parsed by jflex.
   *
   * @param assertion the assertion to be checked.
   */
  private void assertion(boolean assertion)
  {
    if (!assertion) {
      throw new IllegalStateException();
    }
  }

  /**
   * A typesafe enumeration of brace types.
   */
  public static final class BraceType
  {
    /**
     * Subscript enclosed in braces.
     */
    public final static BraceType SUB = new BraceType("SUB");

    /**
     * Superscript enclodes in braces.
     */
    public final static BraceType SUPER = new BraceType("SUPER");

    /**
     * Subscript enclosed in braces and space has to be added after
     * all superscripts and subscripts.
     */
    public final static BraceType SUB_SPACE = new BraceType("SUB_SPACE");

    /**
     * Superscript enclosed in braces and space has to be added after
     * all superscripts and subscripts.
     */
    public final static BraceType SUPER_SPACE = new BraceType("SUPER_SPACE");
    /**
     * All remaining braces.
     */
    public final static BraceType BRACE = new BraceType("BRACE");
    private final String name_;

    /**
     * Only this class can construct instances.
     */
    private BraceType(String name)
    {
      name_ = name;
    }

    public String toString()
    {
      return name_;
    }

    public final int hashCode()
    {
      return super.hashCode();
    }

    public final boolean equals(Object o)
    {
      return super.equals(o);
    }

    public static BraceType fromString(String value)
    {
      if (value.equals("BRACE")) {
        return BRACE;
      }
      if (value.equals("SUB")) {
        return SUB;
      }
      if (value.equals("SUPER")) {
        return SUPER;
      }
      if (value.equals("SUB_SPACE")) {
        return SUB_SPACE;
      }
      if (value.equals("SUPER_SPACE")) {
        return SUB_SPACE;
      }
      throw new IllegalArgumentException();
    }
  }
%}




/* white spaces */
NL = "\n" | "\r"
WS = [\ \t\b\012] | {NL}

/* hard spaces */
HS = "~" | "\\," | "\\:" | "\\;" | "\\ "
  | "\\t1" | "\\t2" | "\\t3" | "\\t4" | "\\t5" | "\\t6" | "\\t7"
  | "\\t8" | "\\t9"
NOT_NL = !(![^] | {NL})
COMMENT = "%" {NOT_NL}* {NL}
IGNORE = {WS} | {COMMENT}

LETTER = [a-zA-Z]
NOT_LETTER = !(![^] | {LETTER})

COMMAND = "\\" . | "\\" {LETTER}*
SCRIPT = "^" | "_"
FUNCTION = "*" | "+" | "-" | "@" | "|"
PUNCTATION = ";" | ","
RELATION = ":" | "<" | "=" | ">"

%state ZED

%%
/* ------------------------Lexical Rules Section---------------------- */

<YYINITIAL> {
  "\\begin" {IGNORE}* "{axdef}"
        {
          yybegin(ZED);
          assertion(!addSpace_);
          return result(ZString.AX);
        }
  "\\begin" {IGNORE}* "{gendef}"
        {
          yybegin(ZED);
          assertion(!addSpace_);
          return result(ZString.GENAX);
        }
  "\\begin" {IGNORE}* "{schema}"
        {
          yybegin(ZED);
          assertion(!addSpace_);
          braceToSpace_ = true;
          return result(ZString.SCH);
        }
  "\\begin" {IGNORE}* ("{zed}" | "{zsection}")
        {
          yybegin(ZED);
          assertion(!addSpace_);
          return result(ZString.ZED);
        }
  {COMMENT}
        {
          return result(yytext());
        }
  [^]
        {
          return result(yytext());
        }
}

<ZED> {
  {IGNORE}
        {
          /* ignore whitespaces and comments */
        }
  {HS}
        {
          String result = addSpace();
          result += ZString.SPACE;
          return result(result);
        }
  "\\\\" | "\\also" | "\\znewpage"
        {
          String result = addSpace();
          return result(result + ZString.NLCHAR);
        }
  "\\end" {IGNORE}* ("{axdef}"|"{gendef}"|"{schema}"|"{zed}"|"{zsection}")
        {
          yybegin(YYINITIAL);
          String result = addSpace();
          return result(result + ZString.END);
        }
  "\\where"
        {
          String result = addSpace();
          return result(result + ZString.SPACE + ZString.VL + ZString.SPACE);
        }
  {SCRIPT} {IGNORE}* ({RELATION}|{PUNCTATION}|{FUNCTION}|{LETTER}|[0-9])
        {
          String script = yytext().substring(0, 1);
          return result(beginScript(script)
                        + yytext().substring(yytext().length() - 1)
                        + endScript(script));
        }
  {SCRIPT} {IGNORE}* {COMMAND}
        {
          String result = "";
          String script = yytext().substring(0, 1);
          String command = yytext().substring(yytext().indexOf("\\"));
          String zstring = LatexMarkup.toUnicode(command, false);
          result += beginScript(script);
          if (zstring != null) {
            result += zstring;
          } else {
            System.err.println("WARNING: Unknown latex command " + command
                               + " at line " + yyline);
            result += command.substring(1);
          }
          result += endScript(script);
          return result(result);
        }
  {SCRIPT} {IGNORE}* "{"
        {
          String script = yytext().substring(0, 1);
          if ("^".equals(script)) {
            if (addSpace_) {
              braceStack_.push(BraceType.SUPER_SPACE);
            } else {
              braceStack_.push(BraceType.SUPER);
            }
          } else if ("_".equals(script)) {
            if (addSpace_) {
              braceStack_.push(BraceType.SUB_SPACE);
            } else {
              braceStack_.push(BraceType.SUB);
            }
          }
          addSpace_ = false;
          return result(beginScript(script));
        }
  {SCRIPT} {IGNORE}* .
        {
          /* TODO: make this a parse error exception */
          throw new UnsupportedOperationException(yytext());
        }
  "\\_" | "\\{" | "\\}"
        {
          String result = addSpace();
          return result(result + yytext().substring(1));
        }
  {COMMAND}
        {
          String result = addSpace();
          boolean spaces = braceStack_.empty();
          String zstring = LatexMarkup.toUnicode(yytext(), false);
          if (zstring != null) {
            LatexMarkup.Type type = LatexMarkup.getType(yytext());
            boolean post = LatexMarkup.Type.POST.equals(type);
            boolean in = LatexMarkup.Type.IN.equals(type);
            boolean pre = LatexMarkup.Type.PRE.equals(type);
            if (spaces && (post || in)) {
              result += ZString.SPACE;
            }
            result += zstring;
            if (spaces && (pre || in)) {
              addSpace_ = true;
            }
          } else {
            System.err.println("WARNING: Unknown latex command " + yytext()
                               + " at line " + yyline);
            if (spaces) result += ZString.SPACE;
            result += yytext().substring(1);
            if (spaces) result += ZString.SPACE;
          }
          return result(result);
        }
  "{"
        {
          String result = addSpace();
          braceStack_.push(BraceType.BRACE);
          return result(result);
        }
  "}"
        {
          String result = "";
          if (braceToSpace_) {
            result += ZString.SPACE;
            braceToSpace_ = false;
          }
          if (braceStack_.empty()) {
            System.err.println("Unmatched braces");
          }
          BraceType brace = (BraceType) braceStack_.pop();
          assertion(!addSpace_);
          if (brace.equals(BraceType.SUPER)) {
            result += ZString.SW;
          } else if (brace.equals(BraceType.SUPER_SPACE)) {
            result += ZString.SW;
            addSpace_ = true;
          } else if (brace.equals(BraceType.SUB)) {
            result += ZString.NW;
          } else if (brace.equals(BraceType.SUB_SPACE)) {
            result += ZString.NW;
            addSpace_ = true;
          }
          return result(result);
        }
  {FUNCTION} | {RELATION}({RELATION}|{WS})*
        {
          String result = addSpace();
          if (braceStack_.empty()) {
            result += ZString.SPACE;
          }
          result += yytext().replaceAll("[ ]", "");
          if (braceStack_.empty()) {
            addSpace_ = true;
          }
          return result(result);
        }
  {PUNCTATION}
        {
          String result = addSpace();
          result += yytext();
          if (braceStack_.empty()) addSpace_ = true;
          return result(result);
        }
  .
        {
          String result = addSpace();
          result += yytext();
          return result(result);
        }
}
