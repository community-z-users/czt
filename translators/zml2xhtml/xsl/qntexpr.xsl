<?xml version="1.0"?> 
<!-- -->
<!-- qntexpr.xsl -->
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
  xmlns:cztext="xalan://net.sourceforge.czt.zmltp.xslextension.NodesetSemanticIntersection"
  xmlns="http://czt.sourceforge.net/zml"
  version="1.0">

  <xsl:template match="Z:SchText" mode="Qnt1ExprDeclarations">    
    <xsl:for-each select="child::*[cztext:isInSubstitutionGroup(., $dsgns/*)]">
      <xsl:apply-templates select="."/>
      <xsl:if test="position() != last()">; </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <xsl:template match="Z:SchText" mode="Qnt1ExprPredicates">
    <xsl:for-each select="child::*[last() and cztext:isInSubstitutionGroup(., $psgns/*)]">
      <xsl:apply-templates select="."/>
    </xsl:for-each>
  </xsl:template>

  <!-- MuExpr -->
  <xsl:template match="Z:MuExpr">
    <xsl:apply-templates select="Z:SchText" mode="Qnt1ExprDeclarations"/>
    <xsl:if test="Z:SchText/child::*[cztext:isInSubstitutionGroup(., $psgns/*)]"> | </xsl:if>
    <xsl:apply-templates select="Z:SchText" mode="Qnt1ExprPredicates"/>
    <xsl:if test="child::*[last() and cztext:isInSubstitutionGroup(., $esgns/*)]">     
      &#x2981;
      <xsl:apply-templates select="child::*[last()]"/>
    </xsl:if>    
  </xsl:template>

  <!-- Render an existential quantifier expression -->
  <xsl:template match="Z:ExistsExpr">
    &#x2203;
    <xsl:apply-templates select="Z:SchText" mode="Qnt1ExprDeclarations"/>
    <xsl:if test="Z:SchText/child::*[cztext:isInSubstitutionGroup(., $psgns/*)]"> | </xsl:if>
    <xsl:apply-templates select="Z:SchText" mode="Qnt1ExprPredicates"/>
    <xsl:if test="child::*[last() and cztext:isInSubstitutionGroup(., $esgns/*)]">     
      &#x2981;
      <xsl:apply-templates select="child::*[last()]"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="Z:Exists1Expr">
    &#x2203;
    <xsl:apply-templates select="Z:SchText" mode="Qnt1ExprDeclarations"/>
    <xsl:if test="Z:SchText/child::*[cztext:isInSubstitutionGroup(., $psgns/*)]"> | </xsl:if>
    <xsl:apply-templates select="Z:SchText" mode="Qnt1ExprPredicates"/>
    <xsl:if test="child::*[last() and cztext:isInSubstitutionGroup(., $esgns/*)]">     
      &#x2981;
      <xsl:apply-templates select="child::*[last()]"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="Z:ForallExpr">
    &#x2200;
    <xsl:apply-templates select="Z:SchText" mode="Qnt1ExprDeclarations"/>
    <xsl:if test="Z:SchText/child::*[cztext:isInSubstitutionGroup(., $psgns/*)]"> | </xsl:if>
    <xsl:apply-templates select="Z:SchText" mode="Qnt1ExprPredicates"/>
    <xsl:if test="child::*[last() and cztext:isInSubstitutionGroup(., $esgns/*)]">     
      &#x2981;
      <xsl:apply-templates select="child::*[last()]"/>
    </xsl:if>    
  </xsl:template>

  <!-- Render a LambdaExpr -->
  <xsl:template match="Z:LambdaExpr">
    LAMDA <xsl:apply-templates select="Z:SchText"/> o <xsl:apply-templates select="child::*[last()]"/>
  </xsl:template>

  <!-- Render a Z LetExpr ('local variable') -->
  <xsl:template match="Z:LetExpr">    
    <div id="keyword">let</div>
    <xsl:for-each select="Z:SchText/Z:ConstDecl">
      <xsl:apply-templates select="Z:DeclName"/> ==
      <xsl:apply-templates select="child::*[last()]"/>
      <xsl:if test="position() != last()">; </xsl:if>
    </xsl:for-each>
    &#x2981;    
    <xsl:apply-templates select="child::*[last()]"/>
  </xsl:template>

  <xsl:template name="QntExpr">    
  </xsl:template>  

</xsl:stylesheet>

