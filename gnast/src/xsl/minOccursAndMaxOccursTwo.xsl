<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:xs="http://www.w3.org/2001/XMLSchema"
  xmlns:jaxb="http://java.sun.com/xml/ns/jaxb">

<xsl:output method="xml"
  encoding="UTF-8"
  indent="yes"/>

<xsl:template match="*[@minOccurs='2' and @maxOccurs='2']">
  <xsl:if test="xs:annotation">
    <xsl:message terminate="yes">
ERROR: Node <xsl:value-of select="name()"/> has already an annotation.
    </xsl:message>
  </xsl:if>
  <xsl:variable name="name">
    <xsl:choose>
      <xsl:when test="@name">
        <xsl:value-of select="@name"/>
      </xsl:when>
      <xsl:when test="@ref">
        <xsl:call-template name="stripNamespace">
          <xsl:with-param name="text" select="@ref"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:message terminate="yes">
ERROR: Cannot find a name since neither a name nor a ref attribute is given.
        </xsl:message>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:variable>
  <xsl:copy>
    <xsl:apply-templates select="@name | @type | @ref"/>
    <xs:annotation>
      <xs:appinfo>
        <jaxb:property>
          <xsl:attribute name="name">
            <xsl:text>Left</xsl:text><xsl:value-of select="$name"/>
          </xsl:attribute>
        </jaxb:property>
      </xs:appinfo>
    </xs:annotation>
    <xsl:apply-templates select="node()"/>
  </xsl:copy>
  <xsl:copy>
    <xsl:apply-templates select="@name | @type | @ref"/>
    <xs:annotation>
      <xs:appinfo>
        <jaxb:property>
          <xsl:attribute name="name">
            <xsl:text>Right</xsl:text><xsl:value-of select="$name"/>
          </xsl:attribute>
        </jaxb:property>
      </xs:appinfo>
    </xs:annotation>
    <xsl:apply-templates select="node()"/>
  </xsl:copy>
</xsl:template>

<xsl:template match="/xs:schema">
  <xsl:copy>
    <xsl:if test="not(@jaxb:version)">
      <xsl:attribute name="jaxb:version">
        <xsl:text>1.0</xsl:text>
      </xsl:attribute>
    </xsl:if>
    <xsl:apply-templates select="@* | node()"/>
  </xsl:copy>
</xsl:template>

<xsl:template match="/ | @* | node()">
  <xsl:copy>
    <xsl:apply-templates select="@* | node()"/>
  </xsl:copy>
</xsl:template>

<!--
     ******************************
     stripNamespace
     ******************************
-->
<xsl:template name="stripNamespace">
  <xsl:param name="text"/>
  <xsl:choose>
    <xsl:when test="contains($text, ':')">
      <xsl:value-of select="substring-after($text, ':')"/>
    </xsl:when>
    <xsl:otherwise>
      <xsl:value-of select="$text"/>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>

</xsl:stylesheet>
