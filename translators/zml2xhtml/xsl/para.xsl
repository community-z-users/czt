<?xml version="1.0"?> 
<!-- -->
<!-- para.xsl -->
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

  <xsl:import href="axpara.xsl"/>
  <xsl:import href="freepara.xsl"/>
  <!-- Templates for Z:ConjPara elements are defined in the current file -->

  <!-- Declaration Substitution Group -->
  <!-- A list of all elements belonging to the Z Schema's 'Para' substitution group -->
  <xsl:variable name="parasg">
    <Z:GivenPara/>
    <Z:AxPara/>
    <Z:FreePara/>
    <Z:ConjPara/>
    <Z:OptempPara/>
    <Z:UnparsedPara/>
    <Z:NarrPara/>
  </xsl:variable>
  <!-- In XSLT 1.0, $ssg is a Result Tree Fragment (RTF) -->
  <!-- Substitution Group Element Lists need to be available as a NodeSet. -->
  <!-- The type conversion from RTF to NodeSet requires the Xalan custom function 'nodeset' -->
  <!-- This conversion will become unnecessary in XSLT 2.0, as the datatype RTF will be discarded and -->
  <!-- all its occurances replaced by the type NodeSet -->
  <xsl:variable name='parasgns' select="xalan:nodeset($parasg)"/>

  <!-- Narrative paragraphs are ignored for the time being -->
  <!-- @todo: this should be configurable with a stylesheet flag (preferrably XSLT input parameter) -->
  <xsl:template match="Z:NarrPara">
    
    <!--    <div id="paragraphdescription">A NarrPara</div> -->
  </xsl:template>

  <!-- Render a Z:GivenPara -->
  <!-- This is basically a list of declarations -->
  <xsl:template match="Z:GivenPara">
    <xsl:text>[</xsl:text>
    <xsl:for-each select="child::*">
      <xsl:apply-templates select="."/>
    </xsl:for-each>
    <xsl:text>]</xsl:text>
  </xsl:template>


  <xsl:template match="Z:UnparsedPara">
    <div id="paragraphdescription">An UnparsedPara</div>
  </xsl:template>

  <xsl:template match="Z:ConjPara">
    <hr/>
    <xsl:apply-templates select="Z:DeclName"/><br/>

    &#x22A2;

    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $psgns/*)]"/>
    <hr/>
  </xsl:template>


</xsl:stylesheet>




