<?xml version="1.0"?> 
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns:cztext="xalan://net.sourceforge.czt.zml2html.xpathextension.NodesetSemanticIntersection"
  xmlns:xalan="http://xml.apache.org/xalan"

  xmlns="http://czt.sourceforge.net/zml"
  version="1.0">

  <xsl:import href="applexpr.xsl"/>
  <xsl:import href="mempred.xsl"/> <!-- required for operator type lookup, see match="Z:RefExpr" template -->
  <xsl:import href="qntexpr.xsl"/>





  <!-- Expression Substitution Group -->
  <!-- A list of all elements belonging to the Z Schema's 'Expr' substitution group -->
  <xsl:variable name="esg">
    <Z:RefExpr/>
    <Z:SchExpr/>
    <Z:NumExpr/>
    <Z:PowerExpr/>
    <Z:SetExpr/>
    <Z:TupleExpr/>
    <Z:ProdExpr/>
    <Z:BindExpr/>
    <Z:TupleSelExpr/>
    <Z:BindSelExpr/>
    <Z:CondExpr/>
    <Z:ApplExpr/>
    <Z:DecorExpr/>
    <Z:ThetaExpr/>
    <Z:RenameExpr/>
    <Z:NegExpr/>
    <Z:PreExpr/>
    <Z:AndExpr/>
    <Z:OrExpr/>
    <Z:ImpliesExpr/>
    <Z:IffExpr/>
    <Z:CompExpr/>
    <Z:PipeExpr/>
    <Z:ProjExpr/>
    <Z:HideExpr/>
    <Z:ForallExpr/>
    <Z:ExistsExpr/>
    <Z:Exists1Expr/>
    <Z:LambdaExpr/>
    <Z:MuExpr/>
    <Z:LetExpr/>
    <Z:SetCompExpr/>
  </xsl:variable>
  <!-- In XSLT 1.0, $esg is a Result Tree Fragment (RTF) -->
  <!-- Substitution Group Element Lists need to be available as a NodeSet. -->
  <!-- The type conversion from RTF to NodeSet requires the Xalan custom function 'nodeset' -->
  <!-- This conversion will become unnecessary in XSLT 2.0, as the datatype RTF will be discarded and -->
  <!-- all its occurances replaced by the type NodeSet -->
  <xsl:variable name='esgns' select="xalan:nodeset($esg)"/>

  <xsl:template name="_get_operator_type">
    <xsl:param name="operator-name"/>

    <xsl:variable name="operator-type-as-textnode">     
      <xsl:apply-templates select="$function-operators-top">
        <xsl:with-param name="index" select="$operator-name"/>          
      </xsl:apply-templates>
      <xsl:apply-templates select="$relation-operators-top">
        <xsl:with-param name="index" select="$operator-name"/>          
      </xsl:apply-templates>
    </xsl:variable>
    <xsl:copy-of select="$operator-type-as-textnode"/>      
  </xsl:template>

  <xsl:template match="Z:RefExpr">

    <xsl:variable name="operator-type-as-textnode">
      <xsl:call-template name="_get_operator_type">
        <xsl:with-param name="operator-name" select="Z:RefName/Z:Word"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="operator-type" select="$operator-type-as-textnode"/>

    <!-- use for-each construct to change context node -->
    <xsl:for-each select="Z:RefName/Z:Word">
      <xsl:choose>
        <xsl:when test="$operator-type = 'infix'">
          (_<xsl:value-of select="."/>_)
        </xsl:when>
        <xsl:when test="$operator-type = 'prefix'">
          (_<xsl:value-of select="."/>)
        </xsl:when>
        <xsl:when test="$operator-type = 'postfix'">
          (<xsl:value-of select="."/>_)
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="."/>
        </xsl:otherwise>
      </xsl:choose>      
    </xsl:for-each>
  </xsl:template>

  <!-- Whats this for? Goota find out before too long :) -->
  <xsl:template match="Z:RefExpr" mode="NotAsSet">
    <xsl:value-of select="Z:RefName/Z:Word"/>
  </xsl:template>

  <!-- ProdExpr -->
  <xsl:template match="Z:ProdExpr">
    &#x300A;
    <xsl:for-each select="child::*[cztext:isInSubstitutionGroup(., $esgns/*)]">      
      <xsl:apply-templates select="."/>
      <xsl:if test="position() != last()"> &#x00D7; </xsl:if>
    </xsl:for-each>
    &#x300B;
  </xsl:template>


  <!-- CondExpr -->
  <xsl:template match="Z:CondExpr">
    <div id="keyword">if</div>
    (<xsl:apply-templates select="child::*[1]"/>)
    <xsl:apply-templates select="child::*[2]"/>;
    <div id="keyword">else</div>
    <xsl:apply-templates select="child::*[2]"/>
  </xsl:template>





  <!-- Renders a schema expression -->
  <xsl:template match="Z:SchExpr">

    <xsl:variable name="pred-count" select="count(Z:SchText/child::*[cztext:isInSubstitutionGroup(., $psgns/*)])"/>

    <xsl:apply-templates select="Z:SchText" mode="DeclarationsSemicolon"/> 
    <xsl:if test="$pred-count > 0">
      | <xsl:apply-templates select="Z:SchText" mode="Predicates"/>      
    </xsl:if>

  </xsl:template>

  <!-- Renders a TupleExpr -->
  <xsl:template match="Z:TupleExpr">
    <xsl:text>(</xsl:text>
    <xsl:for-each select="child::*[cztext:isInSubstitutionGroup(., $esgns/*)]">
      <xsl:apply-templates select="."/>
      <xsl:if test="position() != last()">,</xsl:if>
    </xsl:for-each>
    <xsl:text>)</xsl:text>
  </xsl:template>

  <!-- Renders a NumExpr -->
  <xsl:template match="Z:NumExpr">
    <xsl:value-of select="@Value"/>
  </xsl:template>

  <xsl:template match="Z:SetExpr">
    <xsl:choose>
      <xsl:when test="count(child::*) = 0">
        {}
      </xsl:when>
      <xsl:otherwise>
        {
        <xsl:for-each select="child::*[cztext:isInSubstitutionGroup(., $esgns/*)][1]">
          <xsl:apply-templates select="."/>
        </xsl:for-each>
        }
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Renders a power expression -->
  <!-- Some of the expressions covered by this powerexpression may need brackets at this level) -->
  <!-- NOTE: when did I do this? need to go over -->
  <xsl:template match="Z:PowerExpr">
    &#x2119;<xsl:apply-templates/>
  </xsl:template>

  <!-- -->
  <!-- RENAME EXPRESSION -->
  <!-- -->
  <!-- Renders a Z:RenameExpr element -->
  <xsl:template match="Z:RenameExpr">
    <xsl:apply-templates select="child::*[1]"/>

    [<xsl:for-each select="Z:NameNamePair">
      <xsl:apply-templates select="."/>
      <xsl:if test="position() != last()">, </xsl:if>
    </xsl:for-each>]

  </xsl:template>

  <!-- Renders a Z:NameNamePair as a slash-seperated pair of names -->
  <xsl:template match="Z:NameNamePair">
    <xsl:value-of select="Z:OldName/Z:Word"/>/<xsl:value-of select="Z:NewName/Z:Word"/>
  </xsl:template>

  <!-- -->
  <!-- HIDE EXPRESSION -->
  <!-- -->
  <!-- Renders a Z:HideExpr element -->
  <xsl:template match="Z:HideExpr">
    <xsl:apply-templates select="child::*[1]"/> \

    (<xsl:for-each select="Z:Name">
      <xsl:apply-templates select="." mode="HideExpr"/>
      <xsl:if test="position() != last()">, </xsl:if>
    </xsl:for-each>)
  </xsl:template>

  <xsl:template match="Z:Name" mode="HideExpr">
    <xsl:value-of select="Z:Word"/>
  </xsl:template>

  <!-- -->
  <!-- DECORATION EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:DecorExpr">
    <xsl:apply-templates select="child::*[1]"/>
    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $strokesgns/*)]"/>
  </xsl:template>


  <!-- -->
  <!-- THETA EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:ThetaExpr">
    Q<xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $strokesgns/*)]"/>
    <xsl:apply-templates select="child::*[1]"/>    
  </xsl:template>

  <!-- -->
  <!-- TUPLE SELECTION EXPRESSION -->
  <!-- -->  
  <xsl:template match="Z:TupleSelExpr">
    <xsl:apply-templates select="child::*[1]"/>.<xsl:value-of select="@Select"/>
  </xsl:template>


  <!-- -->
  <!-- BINDING EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:BindExpr">
    &#x300A;
    <xsl:for-each select="Z:NameExprPair">
      <xsl:apply-templates select="."/>
      <xsl:if test="position() != last()">, </xsl:if>
    </xsl:for-each>
    &#x300B;    
  </xsl:template>

  <xsl:template match="Z:NameExprPair">
    <xsl:value-of select="Z:Name/Z:Word"/> =&gt;
    <xsl:apply-templates select="child::*[2]"/>
  </xsl:template>


  <!-- -->
  <!-- BINDING SELECTION EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:BindSelExpr">
    <xsl:apply-templates select="child::*[1]"/>.<xsl:apply-templates select="child::*[2]"/>
  </xsl:template>



  <!-- -->
  <!-- COMPOUND EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:CompExpr">
    <xsl:call-template name="SchExpr2">
      <xsl:with-param name="character" select="'&#x2A1F;'"/>
    </xsl:call-template>
  </xsl:template>


  <!-- -->
  <!-- PIPE EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:PipeExpr">
    <xsl:call-template name="SchExpr2">
      <xsl:with-param name="character" select="'&#x2A20;'"/>
    </xsl:call-template>
  </xsl:template>

  <!-- -->
  <!-- SCHEMA PROJECTION EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:ProjExpr">
    <xsl:call-template name="SchExpr2">
      <xsl:with-param name="character" select="'_whatstheoperator_'"/>
    </xsl:call-template>
  </xsl:template>


  <!-- -->
  <!-- SCHEMA AND EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:AndExpr">
    <xsl:call-template name="SchExpr2">
      <xsl:with-param name="character" select="'&#x2227;'"/>
    </xsl:call-template>
  </xsl:template>

  <!-- -->
  <!-- SCHEMA OR EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:OrExpr">
    <xsl:call-template name="SchExpr2">
      <xsl:with-param name="character" select="'&#x2228;'"/>
    </xsl:call-template>
  </xsl:template>

  <!-- -->
  <!-- SCHEMA IMPLIES EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:ImpliesExpr">
    <xsl:call-template name="SchExpr2">
      <xsl:with-param name="character" select="'&#x21D2;'"/>
    </xsl:call-template>
  </xsl:template>

  <!-- -->
  <!-- SCHEMA IFF EXPRESSION -->
  <!-- -->
  <xsl:template match="Z:IffExpr">
    <xsl:call-template name="SchExpr2">
      <xsl:with-param name="character" select="'&#x21D4;'"/>
    </xsl:call-template>
  </xsl:template>

  <!--
       Helper function to render an expression in the SchExpr2 substitution group.
       -->
  <xsl:template name="SchExpr2">
    <xsl:param name="character"/>
    <xsl:apply-templates select="child::*[1]"/>
    <xsl:value-of select="$character"/>
    <xsl:apply-templates select="child::*[2]"/>
  </xsl:template>

</xsl:stylesheet>


