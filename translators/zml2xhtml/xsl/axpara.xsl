<?xml version="1.0"?> 
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:Z="http://czt.sourceforge.net/zml"
  xmlns="http://czt.sourceforge.net/zml"
  xmlns:cztext="xalan://net.sourceforge.czt.zml2html.xpathextension.NodesetSemanticIntersection"
  version="1.0">

 
 <!-- Template to instantiate whenever a Z:AxPara is encountered.
       This template will perform all required recursive processing
       for the children of Z:AxPara element nodes.
       The rendering style (e.g., box vs no box) depends on the attributes
       and children of the Z:AxPara element
       -->
  <xsl:template match="Z:AxPara">

    <!-- work out @box value -->
    <xsl:variable name='box'>
      <xsl:choose>
        <xsl:when test="not(@Box)">
          <xsl:value-of select="'AxBox'"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="@Box"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    
    <xsl:choose>

      <!-- Schema Definition in box -->
      <xsl:when test="$box='SchBox' and
                      Z:SchText/Z:ConstDecl/Z:SchExpr">
        <xsl:apply-templates select="." mode="SchemaDefBox"/>        
      </xsl:when>

      <!-- Horizontal Definition -->
      <xsl:when test="$box='OmitBox' and
                      Z:SchText/Z:ConstDecl/Z:SchExpr">
        <xsl:apply-templates select="." mode="SchemaDefOmitBox"/>                
      </xsl:when>

      <!-- default: Axiomatic Definition -->
      <xsl:otherwise>
        <xsl:apply-templates select="." mode="axdef"/>
      </xsl:otherwise>
    </xsl:choose> <!-- of AxPara properties based selection -->
  </xsl:template>

  <!-- Renders a Z:AxPara element as an Axiomatic Definition because
       none of the other rendering styles (Schema Definition or Horizontal Definition)
       are applicable to this element node instance -->       
  <xsl:template match="Z:AxPara" mode="axdef">

    <xsl:variable name="decl-count" select="count(Z:SchText/child::*[cztext:isInSubstitutionGroup(., $dsgns/*)])"/>   

    <xsl:apply-templates select="." mode="generics"/>

    <div id='axdef_area'>

      <!-- if there are declarations in this axpara,
           display them one per line -->
      <xsl:if test="$decl-count > 0">
        <div id='axdefdeclarations'>
          <xsl:apply-templates select="Z:SchText" mode="DeclarationsNewline"/>
        </div>        
      </xsl:if>

      <!-- determine the CSS style to use -->
      <!-- (depends on whether there are any declarations -->
      <xsl:variable name="predicate-formatting-style-as-textnode">
        <xsl:choose>
          <xsl:when test="$decl-count > 0">
            axdefpredicates
          </xsl:when>
          <xsl:otherwise>
            axdefpredicates_notopline
          </xsl:otherwise>
        </xsl:choose>
      </xsl:variable>
      <xsl:variable name="predicate-formatting-style" select="normalize-space($predicate-formatting-style-as-textnode)"/>

      <!-- display any predicates if present -->
      <xsl:if test="Z:SchText/child::*[cztext:isInSubstitutionGroup(., $psgns/*)]">
        <div id='{$predicate-formatting-style}'>
          <xsl:apply-templates select="Z:SchText" mode="Predicates"/>
        </div>        
      </xsl:if>
    </div>
  </xsl:template>

  <!-- Renders a Schema Definition in a schema box -->
  <xsl:template match="Z:AxPara" mode="SchemaDefBox">

    <xsl:variable name="decl-count" select="count(Z:SchText/Z:ConstDecl/Z:SchExpr/Z:SchText/child::*[cztext:isInSubstitutionGroup(., $dsgns/*)])"/>
    <xsl:variable name="pred-count" select="count(Z:SchText/Z:ConstDecl/Z:SchExpr/Z:SchText/child::*[cztext:isInSubstitutionGroup(., $psgns/*)])"/>

    <!--    <xsl:apply-templates select="." mode="generics"/>-->

    <!-- determine the CSS style to use -->
    <!-- (depends on whether there are any predicates in the SchText -->
    <xsl:variable name="schema-declarations-style-as-text">
      <xsl:choose>
        <xsl:when test="$pred-count > 0">
          schemadeclarations
        </xsl:when>
        <xsl:otherwise>
          schemadeclarationsnopredicates
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="schema-declarations-style" select="normalize-space($schema-declarations-style-as-text)"/>    

    <div id='schema_area'>
      <div id='schemaheading'>
        <xsl:call-template name="printSchemaHeading"/>
      </div>

      <div id='{$schema-declarations-style}'>
        <xsl:apply-templates select="Z:SchText/Z:ConstDecl/Z:SchExpr/Z:SchText" mode="DeclarationsSemicolon"/>
      </div>        

      <xsl:if test="$pred-count > 0">
        <table id='schemadivline' cellspacing='0' width='100'><tr><td><div id='schemadivline'/></td></tr></table>        
        <div id='schemapredicates'>
          <xsl:apply-templates select="Z:SchText/Z:ConstDecl/Z:SchExpr/Z:SchText" mode="Predicates"/>
        </div>
      </xsl:if>     
    </div>

  </xsl:template>

  <!-- 
       Renders a Schema Definition without a schema box
       -->
  <xsl:template match="Z:AxPara" mode="SchemaDefOmitBox">
    <xsl:value-of select="Z:SchText/Z:ConstDecl/Z:DeclName/Z:Word"/>
    <xsl:if test="count(Z:DeclName) > 0">
      <xsl:apply-templates select="." mode="generics"/>
    </xsl:if>
    ==
    [<xsl:apply-templates select="Z:SchText/Z:ConstDecl/Z:SchExpr"/>]
  </xsl:template>

  <!--
  <xsl:template match="Z:AxPara" mode="GenericSchemaDefOmitBox">
    
    <xsl:apply-templates select="Z:SchText/Z:ConstDecl" mode="SchemaDefOmitBox"/>

    <xsl:apply-tempaltes select="Z:SchText/Z:ConstDecl/Z:SchExpr"

  </xsl:template>
-->

  <!-- *** -->
  <!-- *** Support Templates -->
  <!-- *** -->

  <!-- Selects all those children for processing that are in the XSD substitution group 'Decl' -->
  <xsl:template match="Z:SchText" mode="DeclarationsNewline">
    <xsl:for-each select="child::*[cztext:isInSubstitutionGroup(., $dsgns/*)]">
      <xsl:apply-templates select="."/><br/>        
    </xsl:for-each>
  </xsl:template>

  <!-- Selects all those children for processing that are in the XSD substitution group 'Decl' -->
  <xsl:template match="Z:SchText" mode="DeclarationsSemicolon">
    <xsl:for-each select="child::*[cztext:isInSubstitutionGroup(., $dsgns/*)]">
      <xsl:apply-templates select="."/>
      <xsl:if test="position() != last()">;</xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- Selects all those children for processing that are in the XSD substitution group 'Pred' -->
  <xsl:template match="Z:SchText" mode="Predicates">
    <xsl:apply-templates select="child::*[cztext:isInSubstitutionGroup(., $psgns/*)]"/>
  </xsl:template>

  <!-- prints the heading for the current AxPara -->
  <!-- this template will work for generic axiomatic definitions and generic schema boxes -->
  <!-- context will be AxPara -->
  <xsl:template name="printSchemaHeading">
    <xsl:if test="Z:SchText/Z:ConstDecl"> 
    <xsl:value-of select="Z:SchText/Z:ConstDecl/Z:DeclName/Z:Word"/>
  </xsl:if>
  <xsl:if test="Z:DeclName">
    [ <xsl:call-template name="printDeclNameList"/> ]
  </xsl:if>
  </xsl:template>

  <!-- Will print a list of generics contained a Z:DeclName children of an AxPara -->
  <xsl:template match="Z:AxPara" mode="generics">
    <xsl:variable name="generic-count" select="count(Z:DeclName)"/>
    <xsl:if test="$generic-count > 0">
      [
      <xsl:for-each select="Z:DeclName">
        <xsl:value-of select="."/>
        <xsl:if test="position() != last()">,</xsl:if>
      </xsl:for-each>
      ]
    </xsl:if>    
  </xsl:template>


    

</xsl:stylesheet>









