<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:xs="http://www.w3.org/2001/XMLSchema"
  xmlns:jaxb="http://java.sun.com/xml/ns/jaxb">

<xsl:output method="xml"
  encoding="UTF-8"
  indent="yes"/>
<xsl:strip-space elements="*"/>

<xsl:template match="xs:schema/xs:element[@name!=substring-after(@type, ':')]">
  <xsl:copy>
    <xsl:apply-templates select="@*"/>
    <xsl:attribute name="type">
      <xsl:if test="/xs:schema/@targetNamespace='http://czt.sourceforge.net/zml'">
        <xsl:text>Z:</xsl:text>
      </xsl:if>
      <xsl:if test="/xs:schema/@targetNamespace='http://czt.sourceforge.net/object-z'">
        <xsl:text>OZ:</xsl:text>
      </xsl:if>
      <xsl:if test="/xs:schema/@targetNamespace='http://czt.sourceforge.net/tcoz'">
        <xsl:text>TCOZ:</xsl:text>
      </xsl:if>
      <xsl:if test="/xs:schema/@targetNamespace='http://czt.sourceforge.net/zpatt'">
        <xsl:text>P:</xsl:text>
      </xsl:if>
      <xsl:if test="/xs:schema/@targetNamespace='http://czt.sourceforge.net/circus'">
        <xsl:text>CIRCUS:</xsl:text>
      </xsl:if>
      <xsl:if test="/xs:schema/@targetNamespace='http://czt.sourceforge.net/circuspatt'">
        <xsl:text>CP:</xsl:text>
      </xsl:if>
      <xsl:if test="/xs:schema/@targetNamespace='http://czt.sourceforge.net/circustime'">
        <xsl:text>CT:</xsl:text>
      </xsl:if>
      <xsl:if test="/xs:schema/@targetNamespace='http://czt.sourceforge.net/zeves'">
        <xsl:text>ZEVES:</xsl:text>
      </xsl:if>
      <xsl:value-of select="@name"/>
    </xsl:attribute>
    <xsl:apply-templates select="node()"/>
  </xsl:copy>
</xsl:template>

<xsl:template match="xs:schema">
  <xsl:copy>
    <xsl:apply-templates select="@*"/>
     <xsl:apply-templates select="node()"/>
     <xsl:for-each select="xs:element[@name!=substring-after(@type, ':')]">
       <xs:complexType>
         <xsl:attribute name="name">
           <xsl:value-of select="@name"/>
         </xsl:attribute>
         <xs:complexContent>
           <xs:extension>
             <xsl:attribute name="base">
               <xsl:value-of select="@type"/>
             </xsl:attribute>
           </xs:extension>
         </xs:complexContent>
       </xs:complexType>
      </xsl:for-each>
  </xsl:copy>
</xsl:template>

<xsl:template match="/ | @* | node()">
  <xsl:copy>
    <xsl:apply-templates select="@*"/>
    <xsl:apply-templates select="node()"/>
  </xsl:copy>
</xsl:template>

</xsl:stylesheet>
