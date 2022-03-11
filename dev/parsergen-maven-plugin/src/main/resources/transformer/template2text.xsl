<?xml version="1.0" encoding="utf-8"?>
<xsl:stylesheet
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:add="http://czt.sourceforge.net/templates/additional"
  version="1.0">
  <xsl:output method="text"/>
  <xsl:strip-space elements="*"/>

  <!-- The name of the class to be generated.
       All class nodes are substituted by the value of this paramerter. -->
  <xsl:param name="class"/>
  <!-- The package name of the class to be generated.
       All package noes are substituted by the value of this paramerter. -->
  <xsl:param name="package"/>
  <!-- Additional nodes to be included.
       This contains a list of all node names surrounded by braces
       in namespace http://czt.sourceforge.net/templates/additional
       whos text node should be included in the output.
       For instance if the contents of z and oz nodes should be included
       in the output, add can be set to '{z}, {oz}'.
       The comma can be omitted; this script just searches whether the
       substring '{' + local-name() + '}' is contained. -->
  <xsl:param name="add"/>

  <xsl:template match="*">
    <xsl:apply-templates select="* | text()"/>
  </xsl:template>

  <xsl:template match="add:*">
    <xsl:param name="name" select="concat('{', local-name(.), '}')"/>
    <xsl:if test="contains($add, $name)">
      <xsl:apply-templates select="* | text()"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="class">
    <xsl:value-of select="$class"/>
  </xsl:template>

  <xsl:template match="package">
    <xsl:value-of select="$package"/>
  </xsl:template>

  <xsl:template match="text()">
    <xsl:value-of select="."/>
  </xsl:template>
</xsl:stylesheet>
