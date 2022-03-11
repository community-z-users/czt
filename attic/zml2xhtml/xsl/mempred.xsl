<?xml version="1.0"?> 
<!--
     Stylesheet for rendering the Z:MemPred element.
  -->
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  version="1.1"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns:xalan="http://xml.apache.org/xalan"
  xmlns:cztext="xalan://net.sourceforge.czt.zmltp.xslextension.NodesetSemanticIntersection"
  xmlns:exslt="http://exslt.org/common"
  xmlns:op="http://czt.sourceforgen.net/op"
  xmlns="http://czt.sourceforge.net/zml">

  <xsl:include href='tools.xsl'/>

  <!-- build a  mapping: String->String (Operator Name -> Operator Type) -->
  <!-- types may be prefix, postfix, or infix -->
  <xsl:key name="rel-operator-type-lookup" match="op:operator" use="@name"/>

  <op:relation-operators>
    <op:operator name="=" type="infix"/>
    <op:operator name="disjoint" type="prefix"/>
  </op:relation-operators>

    <!-- load operator list -->
    <xsl:variable name='relation-operators-top' select="document('')/*/op:relation-operators"/>

  <!--
       @desc uses the passed index string to resolve the type of a
          relational operator.
       @param index a construct that string-evaluates to an operator name.
       -->
  <xsl:template match="op:relation-operators">
    <xsl:param name='index'/>
    <xsl:value-of select="key('rel-operator-type-lookup', $index)/@type"/> 
  </xsl:template>

  <!--
       Template to instantiate whenever a Z:MemPred is encountered.
       This template will perform all required recursive processing
       for the children of Z:MemPred element nodes.
       -->
  <xsl:template match="Z:MemPred">

    <!-- determine whether the predicate is to be displayed mixfix -->
    <xsl:variable name="mixfix" select="@Mixfix and (@Mixfix='true()' or @Mixfix='true')"/>

    <!-- resolve operator type -->
    <xsl:variable name='operator-type-as-textnode'>
      <xsl:if test="local-name(child::*[2]) = 'RefExpr'">
        <xsl:apply-templates select="$relation-operators-top">
          <xsl:with-param name="index" select="child::*[2]/Z:RefName/Z:Word"/>          
        </xsl:apply-templates>
      </xsl:if>
    </xsl:variable>
    <xsl:variable name='operator-type' select='$operator-type-as-textnode'/>

    <!-- Test for specific scenarios first, default to standard representation-->
    <xsl:choose>

      <!-- Test for semantically coherent mixfix situation -->
      <xsl:when test="$mixfix=true() and                      
                      local-name(child::*[2]) = 'RefExpr' and
                      (($operator-type='infix' and local-name(child::*[1]) = 'TupleExpr')
                       or $operator-type='prefix' or $operator-type='postfix')">

        <xsl:choose>
          <!-- render an infix operator with mixfix=true -->
          <xsl:when test="$operator-type='infix'">                                   
            <xsl:call-template name="_interweaveTupleExprWithRefExpr">
              <xsl:with-param name="tupleExpr" select="child::*[1]"/>
              <xsl:with-param name="refExpr" select="child::*[2]"/>
            </xsl:call-template>
          </xsl:when>
          <!-- render a prefix operator with mixfix=true -->
          <xsl:when test="$operator-type='prefix'">            
            <xsl:value-of select="child::*[2]/Z:RefName/Z:Word"/>
            <xsl:apply-templates select="child::*[1]"/>
          </xsl:when>
          <!-- render a postfix operator with mixfix=true -->
          <xsl:when test="$operator-type='postfix'">            
            <xsl:apply-templates select="child::*[1]"/>
            <xsl:value-of select="child::*[2]/Z:RefName/Z:Word"/>
          </xsl:when>
        </xsl:choose> <!-- of operator type based selection -->
      </xsl:when>

      <!-- Default rendering of the Z:MemPred element -->
      <xsl:otherwise>
        <xsl:apply-templates select="child::*[1]"/>
        &#x2208;
        <xsl:apply-templates select="child::*[2]"/>                
      </xsl:otherwise>

    </xsl:choose> <!-- of @mixfix based selection -->
  </xsl:template>



</xsl:stylesheet>




