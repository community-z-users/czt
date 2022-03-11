<?xml version="1.0"?> 
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  version="1.1"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns:xalan="http://xml.apache.org/xalan"
  xmlns:cztext="xalan://net.sourceforge.czt.zmltp.xslextension.NodesetSemanticIntersection"
  xmlns:exslt="http://exslt.org/common"
  xmlns:op="http://czt.sourceforgen.et/op"
  xmlns="http://czt.sourceforge.net/zml">


  <!-- Utility for "Rendering MixFix represenations" by
       putting the symbol contained in the refExpr
       parameter in between all the element of the
       tuplExpr
       
       @param tupleExpr the tupleExpr to interweave with symbols
       @param refExpr the symbol to interweave
       -->
  <xsl:template name="_interweaveTupleExprWithRefExpr">
    <xsl:param name="tupleExpr"/>
    <xsl:param name="refExpr"/>
    
    <xsl:for-each select="$tupleExpr/child::*">
      <xsl:apply-templates select="."/>
      <xsl:if test="position() != last()">
        <xsl:value-of select="$refExpr/Z:RefName/Z:Word"/>
      </xsl:if>
    </xsl:for-each>
    
  </xsl:template>

  <!-- Utility for "Wrapping a single expression in a TupleExpr" -->
  <!-- The purpose of this wrapping is to 'normalize' single expressions
       so they can be used as parameter values for named templates
       that expect a Z:TupleExpr type
       -->
  <!-- @param expression2wrap the expression to put into a new TuplExpr -->
  <xsl:template name="_wrapExpressionInTupleExpr">
    <xsl:param name="expression2wrap"/>
    <Z:TupleExpr>
      <xsl:copy-of select="$expression2wrap"/>
    </Z:TupleExpr>
  </xsl:template>






  



</xsl:stylesheet>