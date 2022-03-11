<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:xs="http://www.w3.org/2001/XMLSchema"
  xmlns:jaxb="http://java.sun.com/xml/ns/jaxb">

<xsl:output method="xml"
  encoding="UTF-8"
  indent="yes"/>

<xsl:template match="xs:choice">
  <xsl:copy>
    <xsl:apply-templates select="@*"/>
    <xs:annotation>
      <xsl:apply-templates select="xs:annotation/@* |
                                   xs:annotation/*[not(self::xs:appinfo)]"/>
      <xs:appinfo>
        <xsl:apply-templates select="xs:annotation/xs:appinfo/@* |
                                     xs:annotation/xs:appinfo/*"/>
        <xsl:if test="not(jaxb:property)">
          <jaxb:property>
            <xsl:attribute name="name">
              <xsl:call-template name="selectName">
                <xsl:with-param name="nodes" select="xs:element"/>
              </xsl:call-template>
            </xsl:attribute>
          </jaxb:property>
        </xsl:if>
      </xs:appinfo>
    </xs:annotation>
    <xsl:apply-templates select="node()[not(self::xs:annotation)]"/>
  </xsl:copy>
</xsl:template>

<xsl:template name="selectName">
  <xsl:param name="nodes"/>
  <xsl:for-each select="$nodes">
    <xsl:value-of select="@name"/>
    <xsl:value-of select="substring-after(@ref, ':')"/>
    <xsl:if test="position()!=last()">
      <xsl:text>Or</xsl:text>
    </xsl:if>
  </xsl:for-each>
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

</xsl:stylesheet>
