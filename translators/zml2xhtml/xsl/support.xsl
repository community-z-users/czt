<?xml version="1.0"?> 
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns="http://czt.sourceforge.net/zml"
  version="1.0">

  <!-- Calls xsl:apply-templates to match members of the substitutiongroup $substitutiongroupns, -->
  <!-- where $substitutiongroupns must be the nodeset representation of a substitution group -->
  <!--
       <xsl:template name="recurseSubstitutionGroup">
    <xsl:param name="substitutiongroupns"/>
    <xsl:param name="useMode"/>
    <xsl:for-each select="child::*">
      <xsl:variable name="curchildname" select="local-name(.)"/>
      <xsl:variable name="curchild" select="."/>
      <xsl:for-each select="$substitutiongroupns/*">      
        <xsl:if test="$curchildname = local-name(.)">
          <xsl:choose>
            <xsl:when test="$useMode='useNewline'">
              <xsl:apply-templates select="$curchild" mode="useNewline"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:apply-templates select="$curchild"/>                                    
            </xsl:otherwise>
          </xsl:choose>
        </xsl:if>
      </xsl:for-each>    
    </xsl:for-each>
  </xsl:template>-->

  <!-- outputs first Z:Word element on the child axis of the current nodelist -->
  <xsl:template name="printWord">
    <xsl:value-of select="Z:Word"/>
  </xsl:template>

</xsl:stylesheet>