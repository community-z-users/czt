<?xml version="1.0"?> 
<!-- -->
<!-- sect.xsl -->
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

  <!-- Declaration Substitution Group -->
  <!-- A list of all elements belonging to the Z Schema's 'Sect' substitution group -->
  <xsl:variable name="ssg">
    <Z:ZSect/>
    <Z:UnparsedZSect/>
    <Z:NarrSect/>
  </xsl:variable>
  <!-- In XSLT 1.0, $ssg is a Result Tree Fragment (RTF) -->
  <!-- Substitution Group Element Lists need to be available as a NodeSet. -->
  <!-- The type conversion from RTF to NodeSet requires the Xalan custom function 'nodeset' -->
  <!-- This conversion will become unnecessary in XSLT 2.0, as the datatype RTF will be discarded and -->
  <!-- all its occurances replaced by the type NodeSet -->
  <xsl:variable name='ssgns' select="xalan:nodeset($ssg)"/>

  <!-- renders an unparsed ZSect -->
  <!-- should augment this with CSS -->
  <xsl:template match="Z:UnparsedZSect">
    <hr/>Unparsed Section<hr/>
  </xsl:template>

  <!-- renders a narrative ZSect -->
  <xsl:template match="Z:NarrSect">
    <hr/>Narrative Section<hr/>
  </xsl:template>

  <!-- renders a regular (parsed) ZSect -->
  <xsl:template match="Z:ZSect">
    <p>
      <font size="+2"><b><xsl:value-of select="Z:Name"/></b></font>
      <br/>
      <xsl:if test="Z:Parent">
        parents: 
        <xsl:call-template name="printParentList"/>
        <br/>
      </xsl:if>
    </p>
    <br/>

    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $parasgns/*)]"/>
      
  </xsl:template>

  <xsl:template name="printParentList">
    <xsl:for-each select="Z:Parent">
      <xsl:call-template name="printWord"/>
      <xsl:if test="position() != last()">, </xsl:if>
    </xsl:for-each>
  </xsl:template>

</xsl:stylesheet>