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

  <xsl:key name="fun-operator-type-lookup" match="op:operator" use="@name"/>

  <op:function-precedence-list>
    <op:operator name="+" type='1'/>
    <op:operator name="-" type='1'/>
    <op:operator name="*" type='2'/>
    <op:operator name="/" type='2'/>
    <op:operator name="#" type='3'/>
  </op:function-precedence-list>

  <!-- load operator list -->
  <xsl:variable name='function-precedence-list-top' select="document('')/*/op:function-precedence-list"/>

  <!--
       @desc uses the passed index string to resolve the type of a
          function operator.
       @param index a construct that string-evaluates to an operator name.
       -->
  <xsl:template match="op:function-precedence-list">
    <xsl:param name='index'/>
    <xsl:value-of select="key('fun-operator-type-lookup', normalize-space($index))/@type"/> 
  </xsl:template>

  <xsl:template match="Z:ApplExpr">

    <xsl:copy>
      <xsl:apply-templates select='@*|node()'/>   

      <xsl:choose>
        <xsl:when test="ancestor::Z:ApplExpr[last()]">
          <xsl:variable name="current-applexpr-operator" select="child::*[2]/Z:RefName/Z:Word"/>
          <xsl:variable name="ancestor-applexpr-operator" select="ancestor::Z:ApplExpr[last()]/child::*[2]/Z:RefName/Z:Word"/>
          
          <xsl:variable name='current-operator-precedence-as-textnode'>
            <xsl:if test="local-name(child::*[2]) = 'RefExpr'">
              <xsl:apply-templates select="$function-precedence-list-top">
                <xsl:with-param name="index" select="$current-applexpr-operator"/>          
              </xsl:apply-templates>
            </xsl:if>
          </xsl:variable>
          <xsl:variable name='current-operator-precedence' select='$current-operator-precedence-as-textnode'/>
          
          <xsl:variable name='ancestor-operator-precedence-as-textnode'>
            <xsl:if test="local-name(child::*[2]) = 'RefExpr'">
              <xsl:apply-templates select="$function-precedence-list-top">
                <xsl:with-param name="index" select="$ancestor-applexpr-operator"/>          
              </xsl:apply-templates>
            </xsl:if>
          </xsl:variable>
          <xsl:variable name='ancestor-operator-precedence' select='$ancestor-operator-precedence-as-textnode'/>
          
          <!-- debug
          <xsl:message>
            <xsl:value-of select="'Current: '"/>
            <xsl:value-of select="$current-operator-precedence"/>
          </xsl:message>
          <xsl:message>
            <xsl:value-of select="'Ancestor: '"/>
            <xsl:value-of select="$ancestor-operator-precedence"/>
          </xsl:message>
          -->

          <xsl:if test="$current-operator-precedence &lt; $ancestor-operator-precedence">
            <Z:ParenAnn/>
          </xsl:if>
          
        </xsl:when>
        <xsl:otherwise>
        </xsl:otherwise>
      </xsl:choose>

    </xsl:copy>
       
  </xsl:template>

  <xsl:template match='@*|node()'>
    <xsl:copy>
      <xsl:apply-templates select='@*|node()'/>
    </xsl:copy>
  </xsl:template>

</xsl:stylesheet>