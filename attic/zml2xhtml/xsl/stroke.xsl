<?xml version="1.0"?> 
<!-- -->
<!-- decorations.xsl -->
<!-- -->
<!-- -->
<!-- -->
<!-- @author: Gerret Apelt -->
<!-- @date: $date$ -->
<!-- @version: $version$ -->
<!-- -->
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns:xalan="http://xml.apache.org/xalan"
  xmlns:cztext="xalan://net.sourceforge.czt.zml2html.xpathextension.NodesetSemanticIntersection"
  xmlns="http://czt.sourceforge.net/zml"
  version="1.0">

  <!-- Decoration Substitution Group -->
  <!-- A list of all elements belonging to the Z Schema's 'Stroke' substitution group -->
  <xsl:variable name="strokesg">
    <Z:InStroke/>
    <Z:OutStroke/>
    <Z:NumStroke/>
    <Z:NextStroke/>
  </xsl:variable>
  <!-- In XSLT 1.0, $strokesg is a Result Tree Fragment (RTF) -->
  <!-- Substitution Group Element Lists need to be available as a NodeSet. -->
  <!-- The type conversion from RTF to NodeSet requires the Xalan custom function 'nodeset' -->
  <!-- This conversion will become unnecessary in XSLT 2.0, as the datatype RTF will be discarded and -->
  <!-- all its occurances replaced by the type NodeSet -->
  <xsl:variable name='strokesgns' select="xalan:nodeset($strokesg)"/>

  <xsl:template match="Z:InStroke">?</xsl:template>
  <xsl:template match="Z:OutStroke">!</xsl:template>
  <xsl:template match="Z:NumStroke">
    <sup><xsl:value-of select="@Number"/></sup>
  </xsl:template>
  <xsl:template match="Z:NextStroke">'</xsl:template>

</xsl:stylesheet>





