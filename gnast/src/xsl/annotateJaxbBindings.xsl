<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:xs="http://www.w3.org/2001/XMLSchema"
  xmlns:jaxb="http://java.sun.com/xml/ns/jaxb">

<xsl:output method="xml"
  encoding="UTF-8"
  indent="yes"/>
<xsl:strip-space elements="*"/>

<xsl:template match="xs:schema/xs:element[@name=substring-after(@type, ':') and
                     not(xs:annotation/xs:appinfo/jaxb:class)]">
  <xsl:copy>
    <xsl:apply-templates select="@*"/>
    <xs:annotation>
      <xsl:apply-templates select="xs:annotation/*[not(self::xs:appinfo)]"/>
      <xs:appinfo>
        <xsl:apply-templates select="xs:annotation/xs:appinfo/*"/>
        <jaxb:class>
          <xsl:attribute name="name"><xsl:value-of select="@name"/>Element</xsl:attribute>
        </jaxb:class>
      </xs:appinfo>
    </xs:annotation>
    <xsl:apply-templates select="*[not(self::xs:annotation)]"/>
  </xsl:copy>
</xsl:template>

<xsl:template match="/ | @* | node()">
  <xsl:copy>
    <xsl:apply-templates select="@*"/>
    <xsl:apply-templates select="node()"/>
  </xsl:copy>
</xsl:template>

</xsl:stylesheet>
