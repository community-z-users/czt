<?xml version="1.0" encoding="utf-8"?>
<xsl:transform xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                version="1.0">

  <xsl:output method="text"/>

  <xsl:template match="/">
    <xsl:text>package net.sourceforge.czt.scanner;

import java_cup.runtime.*;

/* ------------Declaration of Terminals and Non Terminals Section----------- */

</xsl:text>
      <xsl:apply-templates select="//token"/>
    <xsl:text>
non terminal Object    input;

/* ----------------------------Grammar Section-------------------- */

   input ::= 
             ;
</xsl:text>
  </xsl:template>

  <xsl:template match="token">
    <xsl:text>terminal </xsl:text>
    <xsl:value-of select="@type"/>
    <xsl:text>   </xsl:text>
    <xsl:value-of select="@id"/>
    <xsl:value-of select="@ref"/>
    <xsl:text>;
</xsl:text>
  </xsl:template>
</xsl:transform>
