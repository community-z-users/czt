<?xml version="1.0"?> 
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns:cztext="xalan:///net.sourceforge.czt.zml2html.xpathextension.NodesetSemanticIntersection"  
  xmlns:cztqa="http://czt.sourceforge.net/cztqa"
  xmlns="http://czt.sourceforge.net/cztqa"
  version="1.0">

  <xsl:output method="html" encoding="UTF-8" indent="yes"/>

  <xsl:template match="cztqa:testcase">
    <table cellpadding='5' bgcolor='lightgrey' width='100%'>
      <tr>
        <td valign='top' width='10%'>Description:</td>
        <td><xsl:apply-templates select="cztqa:description"/></td>
      </tr>
      <xsl:if test="cztqa:note">
        <tr>
          <td valign='top'>
            Notes
          </td>
          <td>
            <xsl:for-each select="cztqa:note">
              <li><xsl:apply-templates select="."/></li>
            </xsl:for-each>
          </td>
        </tr>
      </xsl:if>
    </table>
  </xsl:template>

  <xsl:template match="cztqa:description">    
    <xsl:value-of select="."/>
  </xsl:template>

  <xsl:template match="cztqa:note">    
    <xsl:value-of select="."/>
  </xsl:template>


</xsl:stylesheet>