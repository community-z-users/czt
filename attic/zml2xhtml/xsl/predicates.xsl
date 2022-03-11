<?xml version="1.0"?> 
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns:xalan="http://xml.apache.org/xalan"
  xmlns:cztext="xalan://net.sourceforge.czt.zml2html.xpathextension.NodesetSemanticIntersection"
  xmlns="http://czt.sourceforge.net/zml"
  version="1.0">

  <xsl:import href="mempred.xsl"/>
  <xsl:import href="qntpred.xsl"/>

  <!-- Predicate Substitution Group -->
  <!-- A list of all elements belonging to the Z Schema's 'Pred' substitution group -->
  <xsl:variable name="psg">
    <AndPred/>
    <ExprPred/>
    <NegPred/>
    <OrPred/>
    <ImpliesPred/>
    <IffPred/>
    <ForallPred/>
    <ExistsPred/>
    <Exists1Pred/>
    <MemPred/>
    <FalsePred/>
    <TruePred/>
  </xsl:variable>
  <!-- In XSLT 1.0, $psg is a Result Tree Fragment (RTF) -->
  <!-- Substitution Group Element Lists need to be available as a NodeSet. -->
  <!-- The type conversion from RTF to NodeSet requires the Xalan custom function 'nodeset' -->
  <!-- This conversion will become unnecessary in XSLT 2.0, as the datatype RTF will be discarded and -->
  <!-- all its occurances replaced by the type NodeSet -->
  <xsl:variable name="psgns" select="xalan:nodeset($psg)"/>
  
  <!-- renders an AndPred element -->
  <!-- MarkQ: When an AndPred with Op="NL" is displayed in a schema def or axdef with box="omit", should the Op="NL" be -->
  <!-- MarkQ: overridden, or is it illegal for this case to occur? -->
  <xsl:template match="Z:AndPred">
    <!-- Emulate XSD default @Op value 'And' -->
    <xsl:variable name="Op">
      <xsl:choose>
        <xsl:when test="@Op = ''">
          <xsl:value-of select="'And'"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="@Op"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>

    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $psgns/*)][1]"/>

    <xsl:choose>
      <xsl:when test="$Op = 'And'">
        &#x2227;        
      </xsl:when>
      <xsl:when test="$Op = 'NL'">
        <br/>
      </xsl:when>
      <xsl:when test="$Op = 'Semi'">
        ;
      </xsl:when>
      <!-- MarkQ: how to render the chain attribute value for Op? -->
      <xsl:when test="$Op = 'Chain'">
        Chain
      </xsl:when>
    </xsl:choose>

    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $psgns/*)][2]"/>

  </xsl:template>
  
  <!-- renders an OR predicate -->
  <xsl:template match="Z:OrPred">
    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $psgns/*)][1]"/>
    &#x2228;
    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $psgns/*)][2]"/>
  </xsl:template>


  <!-- Renders the keyword 'true' -->
  <!-- @gnote: This should be formatted by CSS somehow, but not using the
       DIV tag because it causes linebreaks -->
  <xsl:template match="Z:TruePred">
    true
  </xsl:template>

  <xsl:template match="Z:FalsePred">
    true
  </xsl:template>


  <!-- MarkQ: Does this do anything else? -->
  <!--  <xsl:template match="Z:ExprPred">
    <xsl:apply-templates select="child::*"/>
  </xsl:template>-->

</xsl:stylesheet>




