<?xml version="1.0"?> 
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns="http://czt.sourceforge.net/zml"
  xmlns:cztext="xalan://net.sourceforge.czt.zmltp.xslextension.NodesetSemanticIntersection"
  version="1.0">

   <xsl:template match="Z:FreePara">     
     <xsl:apply-templates/>
   </xsl:template>

   <xsl:template match="Z:Freetype">
     <xsl:value-of select="Z:DeclName/Z:Word"/> ::=
     <xsl:for-each select="Z:Branch">
       <xsl:apply-templates select="."/>
       <xsl:if test="position() != last()"> | </xsl:if>
     </xsl:for-each>     
   </xsl:template>

   <xsl:template match="Z:Branch">
     <xsl:value-of select="Z:DeclName/Z:Word"/>
     <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $esgns/*)]"/>
   </xsl:template>


    

</xsl:stylesheet>









