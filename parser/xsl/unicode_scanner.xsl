<?xml version="1.0" encoding="utf-8"?>
<xsl:transform xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                version="1.0">

  <xsl:output method="text"/>

  <xsl:variable name="NL">
    <xsl:text>
</xsl:text>
  </xsl:variable>

  <xsl:template match="/">
    <xsl:text>
/* --------------------------Usercode Section------------------------ */
package net.sourceforge.czt.scanner;

import java_cup.runtime.*;
      
%%
   
/* -----------------Options and Declarations Section----------------- */
   
%class Lexer
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
	System.out.print(message);
    }
%}
   

/* Macro Declarations */

nl = \r|\n|\r\n
whitespace = [\n\r\ \t\b\012]
</xsl:text>
    <xsl:apply-templates select="//ZCHAR/*"/>
    <xsl:text>
ONE       = "1"
DECORWORD = {WORD} {STROKE}*
WORD =   {WORDPART}+ | {LETTER} {ALPHASTR} {WORDPART}* | {SYMBOL}+ {WORDPART}*
WORDPART = {WORDGLUE} ( {ALPHASTR} | {SYMBOL}* )
ALPHASTR = ({LETTER} | {DIGIT})*
NUMERAL = {DIGIT}+
STROKE = {STROKECHAR} | {SE} {DIGIT} {NW}

%%
/* ------------------------Lexical Rules Section---------------------- */
   
&lt;YYINITIAL&gt; {

</xsl:text>
    <xsl:apply-templates select="//TOKEN/*"/>
    <xsl:apply-templates select="//AlphabeticKeywords/*"/>
    <xsl:apply-templates select="//SymbolicKeywords/*"/>
    <xsl:text>
  {NUMERAL}          { return symbol(sym.NUMERAL, new Integer(yytext())); }
  {DECORWORD}        { return symbol(sym.DECORWORD, yytext()); }
  {STROKE}           { return symbol(sym.STROKE, yytext()); }

  {nl}               { log("\n"); }
  {whitespace}       { }
}

/* No token was found for the input so through an error.  Print out an
   Illegal character message with the illegal character that was found. */
[^]                  { throw new Error("Illegal character &lt;"+yytext()+"&gt;"); }

</xsl:text>
  </xsl:template>

  <!-- ZCHAR -->

  <xsl:template match="char">
    <xsl:value-of select="@id"/>
    <xsl:text> = "\u</xsl:text>
    <xsl:value-of select="@hex"/>
    <xsl:text>"</xsl:text>
    <xsl:value-of select="$NL"/>
  </xsl:template>

  <xsl:template match="*[@regexp]">
    <xsl:value-of select="name()"/>
    <xsl:text> = </xsl:text>
    <xsl:value-of select="@regexp"/>
    <xsl:value-of select="$NL"/>
  </xsl:template>

  <xsl:template match="*">
    <xsl:value-of select="name()"/>
    <xsl:text> = </xsl:text>
    <xsl:for-each select="*">
      <xsl:text>{</xsl:text>
      <xsl:choose>
        <xsl:when test="name()='char'">
          <xsl:value-of select="@id"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="name()"/>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:text>}</xsl:text>
      <xsl:if test="position()!=last()">
        <xsl:text> | </xsl:text>
      </xsl:if>
    </xsl:for-each>
    <xsl:value-of select="$NL"/>
    <xsl:apply-templates select="*"/>
  </xsl:template>

  <!-- TOKEN -->

  <xsl:template match="token[@type]">
  </xsl:template>

  <xsl:template match="token[@regexp]">
    <xsl:text>  "</xsl:text>
    <xsl:value-of select="@regexp"/>
    <xsl:text>"   { return symbol(sym.</xsl:text>
    <xsl:value-of select="@id"/>
    <xsl:text>); }</xsl:text>
    <xsl:value-of select="$NL"/>
  </xsl:template>

  <xsl:template match="token[@ref]">
    <xsl:text>  {</xsl:text>
    <xsl:value-of select="@ref"/>
    <xsl:text>}   { return symbol(sym.</xsl:text>
    <xsl:value-of select="@ref"/>
    <xsl:text>); }</xsl:text>
    <xsl:value-of select="$NL"/>
  </xsl:template>

  <xsl:template match="token">
    <xsl:for-each select="char">
      <xsl:text>  {</xsl:text>
      <xsl:value-of select="@ref"/>
      <xsl:text>} </xsl:text>
    </xsl:for-each>
    <xsl:text>   { return symbol(sym.</xsl:text>
    <xsl:value-of select="@id"/>
    <xsl:text>); }</xsl:text>
    <xsl:value-of select="$NL"/>
  </xsl:template>

</xsl:transform>
