<?xml version="1.0"?> 
<!-- -->
<!-- declarations.xsl -->
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
  <!-- A list of all elements belonging to the Z Schema's 'Decl' substitution group -->
  <xsl:variable name="dsg">
    <Z:VarDecl/>
    <Z:ConstDecl/>
    <Z:InclDecl/>
  </xsl:variable>
  <!-- In XSLT 1.0, $dsg is a Result Tree Fragment (RTF) -->
  <!-- Substitution Group Element Lists need to be available as a NodeSet. -->
  <!-- The type conversion from RTF to NodeSet requires the Xalan custom function 'nodeset' -->
  <!-- This conversion will become unnecessary in XSLT 2.0, as the datatype RTF will be discarded and -->
  <!-- all its occurances replaced by the type NodeSet -->
  <xsl:variable name='dsgns' select="xalan:nodeset($dsg)"/>

  <!-- currently un-used, since DeclNames are rendered by the procedure-template printDeclNameList -->
  <xsl:template match="Z:DeclName">    
    <xsl:value-of select="Z:Word"/>
    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $strokesgns)]"/>
  </xsl:template>

  <!-- *** -->
  <!-- *** Decl Substitution Group Elements' Master Templates (3) *** -->
  <!-- *** -->

  <!-- Render a VarDecl element -->
  <xsl:template name="ZVarDecl" match="Z:VarDecl">
    <xsl:call-template name="printDeclNameList"/>:
    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $esgns/*)]"/>
  </xsl:template>

  <!-- Render a ConstDecl element -->
  <!-- @gnote: I should check out (i.e., find) all the constructs and scenarios where ConstDecl is used
       (different modes) and possibly group all the ConstDecl templates here.
       -->
  <xsl:template match="Z:ConstDecl">
    <xsl:value-of select="Z:DeclName/Z:Word"/>==
    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $esgns/*)]"/>
  </xsl:template>

  <!-- Render a ConstDecl element for a boxless schema definition -->
  <!-- This is a special caseof the ConstDecl element, because it is used to define a
       schema expression, which is rendered in a special way -->
  <!-- This template is used both for SchemaDedOmitBox and GenericSchemaDefOmitBox -->
  <xsl:template match="Z:ConstDecl" mode="SchemaDefOmitBox">
    == [<xsl:apply-templates select="Z:SchExpr"/>]
  </xsl:template>


  <!-- Render an InclDecl element -->
  <xsl:template match="Z:InclDecl">
    An Incl(?) Declaration<br/>
  </xsl:template>


  <!-- *** -->
  <!-- *** Support Templates for Decl substitution group *** -->
  <!-- *** -->

  <!-- Output a comma-delimited list of stroke-suffixed DeclNames -->
  <xsl:template name="printDeclNameList">
    <xsl:for-each select="Z:DeclName">
      <xsl:call-template name="printDeclName"/>
      <xsl:if test="position() != last()">, </xsl:if>    
    </xsl:for-each>
  </xsl:template>

  <!-- Output a stroke-suffixed DeclName -->
  <xsl:template name="printDeclName">
    <xsl:value-of select="Z:Word"/>
    <xsl:call-template name="printStrokes"/>
  </xsl:template>

  <!-- Output all strokes on the current child axis -->
  <xsl:template name="printStrokes">
    <xsl:for-each select="Z:InStroke | Z:OutStroke | Z:NextStroke | Z:NumStroke">
      <!--
           XXX: the tests below rely on local-name() for matching node names.
           therefore the tests ignore the namespace of the nodes for matching purposes
           a node from a different namespace (e.g. gerret:InStroke) would be matched
           even though it belongs to a different namespace
           -->
      <xsl:choose>
        <xsl:when test="local-name() = 'InStroke'">?</xsl:when>
        <xsl:when test="local-name() = 'OutStroke'">!</xsl:when>
        <xsl:when test="local-name() = 'NextStroke'">'</xsl:when>
        <xsl:when test="local-name() = 'NumStroke'"><sub><xsl:value-of select="@Number"/></sub></xsl:when>
      </xsl:choose>
    </xsl:for-each>    
  </xsl:template>


</xsl:stylesheet>





