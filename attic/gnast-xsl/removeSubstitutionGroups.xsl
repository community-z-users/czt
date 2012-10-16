<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:xs="http://www.w3.org/2001/XMLSchema"
  xmlns:jaxb="http://java.sun.com/xml/ns/jaxb"
  jaxb:version="1.0"
  xmlns:xalan="http://xml.apache.org/xslt">

<xsl:output method="xml"
  encoding="UTF-8"
  indent="yes"
  xalan:indent-amount="2"/>
<xsl:strip-space elements="*"/>

<xsl:key name="globalElement" match="xs:schema/xs:element" use="@name"/>
<xsl:key name="sg" match="xs:element" use="substring-after(@substitutionGroup, ':')"/>

<xsl:template match="xs:schema">
  <xsl:copy>
    <xsl:apply-templates select="@*"/>
    <xsl:attribute name="jaxb:version">
      <xsl:text>1.0</xsl:text>
    </xsl:attribute>
    <xsl:apply-templates select="node()"/>
  </xsl:copy>
</xsl:template>

<xsl:template match="@substitutionGroup"/>
<xsl:template match="xs:element[@abstract='true']"/>

<xsl:template match="xs:element[@ref]">
  <xsl:variable name="name">
    <xsl:value-of select="substring-after(@ref, ':')"/>
  </xsl:variable>
  <xsl:choose>
    <xsl:when test="key('sg', $name)">
      <xs:choice>
        <xsl:apply-templates select="@minOccurs | @maxOccurs"/>
        <xs:annotation>
          <xs:appinfo>
            <jaxb:property>
              <xsl:attribute name="name">
                <xsl:choose>
                  <xsl:when test="xs:annotation/xs:appinfo/jaxb:property/@name">
                    <xsl:value-of select="xs:annotation/xs:appinfo/jaxb:property/@name"/>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:value-of select="$name"/>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:attribute>
            </jaxb:property>
          </xs:appinfo>
        </xs:annotation>
        <xsl:call-template name="collectElementsInSubstitutionGroup">
          <xsl:with-param name="element" select="key('globalElement', $name)"/>
        </xsl:call-template>
      </xs:choice>
    </xsl:when>
    <xsl:otherwise>
      <xsl:copy-of select="."/>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>

<xsl:template name="collectElementsInSubstitutionGroup">
  <xsl:param name="element"/>
  <xsl:for-each select="$element">
    <xsl:if test="not(@abstract='true')">
      <xs:element>
        <xsl:attribute name="ref">
          <xsl:value-of select="concat('Z:', @name)"/>
        </xsl:attribute>
      </xs:element>
    </xsl:if>
    <xsl:call-template name="collectElementsInSubstitutionGroup">
      <xsl:with-param name="element" select="key('sg', @name)"/>
    </xsl:call-template>
  </xsl:for-each>
</xsl:template>


<xsl:template match="/ | @* | node()">
  <xsl:copy>
    <xsl:apply-templates select="@* | node()"/>
  </xsl:copy>
</xsl:template>

</xsl:stylesheet>
