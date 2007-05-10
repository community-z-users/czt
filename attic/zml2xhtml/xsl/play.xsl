<?xml version="1.0"?> 
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
  xmlns:Z="http://web.comlab.ox.ac.uk/oucl/work/andrew.martin/CZT/zstd.xsd"
  xmlns="http://web.comlab.ox.ac.uk/oucl/work/andrew.martin/CZT/zstd.xsd"
  version="1.0">

  <xsl:output method="html" encoding="UTF-8" indent="yes"/>

  <xsl:template match="Z:Spec">
    <html>
      <head>
        <title>Spec</title>
      </head>
      <body>
        <p><a href="output.txt">source</a></p>
        <xsl:apply-templates/>
      </body>
    </html>
  </xsl:template>

  <xsl:template match="Z:ZSect">
    <font size="+2">Section <font color="red"><xsl:value-of select="Z:Name"/></font></font><br/>
    <xsl:choose>
      <xsl:when test="count(Z:Name) != 0">
        Parents: <xsl:apply-templates select="Z:Parent"/>
      </xsl:when>
    </xsl:choose>
    <p/>
    <xsl:apply-templates select="Z:GivenPara | Z:NarrPara | Z:AxPara | Z:UnparsedPara"/>
  </xsl:template>

  <xsl:template match="Z:Parent">
    <xsl:value-of select="Z:Word"/>
  </xsl:template>

  <xsl:template match="Z:GivenPara">
    <table bgcolor="lightblue" size="90%">
      <tr>
        <td><h3>Given Para</h3></td>
      </tr>
      <xsl:apply-templates select="Z:DeclName"/>        
    </table>
  </xsl:template>

  <xsl:template match="Z:DeclName">
    <tr><td><xsl:value-of select="."/></td></tr>
  </xsl:template>

  <xsl:template match="Z:NarrPara">
    <!--    <p>Narrative Para</p> -->

    <p><xsl:apply-templates/></p>
  </xsl:template>


  <!-- Axiomatic Paragraph -->
  <xsl:template match="Z:AxPara">
    <table bgcolor="lightgreen" size="90%">
      <tr>
        <td><h3>Axiomatic Para</h3></td>
      </tr>
	<!-- <img src="gfx/horizontal_line.jpg"/> -->
	<img src="file:///home/ga11/zml/play/gfx/vertical_line.jpg" align="left"/>
      <xsl:apply-templates/>
    </table>
	<img src="file:///home/ga11/zml/play/gfx/horizontal_line.jpg" align="textbottom"/>	
  </xsl:template>

  <xsl:template match="Z:SchText">
    <xsl:for-each select="Z:VarDecl">
      <tr><td><xsl:call-template name="VariableDeclList"/></td></tr>
    </xsl:for-each>    
  </xsl:template>

  <xsl:template name="VariableDeclList">
    <xsl:for-each select="Z:DeclName">
      <xsl:value-of select="Z:Word"/>
      <xsl:if test="position()!=last()">, </xsl:if> 
    </xsl:for-each>:
    <xsl:apply-templates select="Z:RefExpr"/>
  </xsl:template>

  <xsl:template match="Z:RefExpr">
    <xsl:value-of select="Z:RefName/Z:Word"/>
  </xsl:template>

  <xsl:template match="Z:UnparsedPara">
    <table size="90%" bgcolor="lightgrey">
      <tr>
        <td>
          <h3>Unparsed Para</h3>          
        </td>
      </tr>
      <tr>
        <td>
          <xsl:apply-templates/>
        </td>
      </tr>
    </table>
  </xsl:template>

</xsl:stylesheet>



