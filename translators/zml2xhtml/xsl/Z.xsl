<?xml version="1.0"?> 
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns:xalan="http://xml.apache.org/xalan"
  xmlns:cztext="xalan://net.sourceforge.czt.zml2html.xpathextension.NodesetSemanticIntersection"
  xmlns:testing="http://czt.sourceforge.net/zml/zml2html/testing"
  version="1.0">

  <xsl:import href="predicates.xsl"/>
  <xsl:import href="expressions.xsl"/>
  <xsl:import href="declarations.xsl"/>
  <xsl:import href="sect.xsl"/>
  <xsl:import href="support.xsl"/>
  <xsl:import href="para.xsl"/> <!-- includes axpara.xsl -->
  <xsl:import href="cztqa.xsl"/>
  <xsl:import href="stroke.xsl"/>

  <xsl:strip-space elements="*"/>

  <!--  <xsl:output method="html" encoding="UTF-8" indent="yes"/>-->

  <xsl:template match="Z:Spec">
    <html>
      <head>
        <title>Spec</title>
        <link rel="stylesheet" type="text/css" href="zstyle.css"/>
      </head>
      <body>
        <br/>
        <!--        <xsl:apply-templates select="Z:Anns/cztqa:testcase"/>-->
        <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $ssgns/*)]"/>
      </body>
    </html>
  </xsl:template>
  

</xsl:stylesheet>


