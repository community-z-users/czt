<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<!-- This XSLT stylesheet adds a CZT header and left-hand sidebar
     onto a page of html content.  The input page should be in
     XML format.

     If the 'pagename' variable matches one of the links in the sidebar,
     then that link is highlighted with an arrow rather than a bullet, to
     indicate it is the current page.  
--> 

<xsl:output method="html"
  encoding="UTF-8"
  doctype-system="http://www.w3c.org/TR/1999/REC-html401-19991224/loose.dtd"
  doctype-public="-//W3C//DTD HTML 4.01 Transitional//EN"/>

<xsl:param name="pagename" select="'Home'"/>
<xsl:param name="homedir" select="'.'"/>
<xsl:param name="imagedir">
  <xsl:value-of select="$homedir"/>
  <xsl:text>/images</xsl:text>
</xsl:param>


<xsl:variable name="lowercase" select="'abcdefghijklmnopqrstuvwxyz'"/>
<xsl:variable name="uppercase" select="'ABCDEFGHIJKLMNOPQRSTUVWXYZ'"/>

<xsl:template name="toclink">
  <xsl:param name="name"/>
  <xsl:param name="url"/>
  <xsl:variable name="lowername"
      select="translate($name,$uppercase,$lowercase)"/>
  <xsl:choose>
    <xsl:when test="$pagename=$lowername">
      <img border="0" alt="--&gt; " width="20" height="15">
        <xsl:attribute name="src">
          <xsl:value-of select="$imagedir"/>
          <xsl:text>/arrow.gif</xsl:text>
        </xsl:attribute>
      </img>
    </xsl:when>
    <xsl:otherwise>
      <img border="0" alt="* " width="16" height="12">
        <xsl:attribute name="src">
          <xsl:value-of select="$imagedir"/>
          <xsl:text>/bullet.gif</xsl:text>
        </xsl:attribute>
      </img>
    </xsl:otherwise>
  </xsl:choose>
  <a>
    <xsl:attribute name="href">
      <xsl:value-of select="$url"/>
    </xsl:attribute>
    <xsl:value-of select="$name"/>
  </a><p/>
</xsl:template>

<xsl:template match="/content">
<html>
<head>
  <title>CZT <xsl:value-of select="$pagename"/></title>
  <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1"/>
  <meta http-equiv="Content-Language" content="en-us"/>
  <meta http-equiv="Author" content="Mark Utting"/>
</head>

<body bgcolor="#87a7ff" link="#1c32ff" vlink="#0d1777" alink="#FF0000">

<div align="left">
  <table border="0" cellpadding="10" cellspacing="0" width="100%">
    <tr>

      <td align="right" valign="top" width="15%" height="150">
        <img border="0" alt="CZT logo" width="150" height="150">
          <xsl:attribute name="src">
            <xsl:value-of select="$imagedir"/>
            <xsl:text>/cztlogo150.jpg</xsl:text>
          </xsl:attribute>
        </img>
      </td>
      <td valign="bottom" height="150">
        <img border="0" alt="CZT: Community Z Tools" height="150">
          <xsl:attribute name="src">
            <xsl:value-of select="$imagedir"/>
            <xsl:text>/czttitle150.jpg</xsl:text>
          </xsl:attribute>
        </img>
      </td>
    </tr>
    <tr>
      <td valign="top" width="15%">
        <p/>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'Home'"/>
          <xsl:with-param name="url" select="'http://czt.sourceforge.net'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'CZT@Oxford...'"/>
          <xsl:with-param name="url" select="'http://web.comlab.ox.ac.uk/oucl/work/andrew.martin/CZT'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'What is Z?...'"/>
          <xsl:with-param name="url" select="'http://www.zuser.org/z'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'ZML'"/>
          <xsl:with-param name="url" select="'zml'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'News'"/>
          <xsl:with-param name="url">
            <xsl:value-of select="$homedir"/>
            <xsl:text>/news.html</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'People'"/>
          <xsl:with-param name="url">
            <xsl:value-of select="$homedir"/>
            <xsl:text>/people.html</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'Screenshots'"/>
          <xsl:with-param name="url">
            <xsl:value-of select="$homedir"/>
            <xsl:text>/screenshots.html</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'Documentation'"/>
          <xsl:with-param name="url">
            <xsl:value-of select="$homedir"/>
            <xsl:text>/documentation.html</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'Development'"/>
          <xsl:with-param name="url" select="'http://sourceforge.net/projects/czt'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'Downloads'"/>
          <xsl:with-param name="url" select="'http://sourceforge.net/project/showfiles.php?group_id=86250'"/>
        </xsl:call-template>
        <p/>
        <a href="http://sourceforge.net"><img src="http://sourceforge.net/sflogo.php?group_id=86250&amp;type=4" width="125" height="37" border="0" alt="SourceForge.net Logo" /></a>
      </td>
      <td valign="top" bgcolor="#d8d8d8">
        <xsl:for-each select="* | text()">
          <xsl:copy-of select="."/>
        </xsl:for-each>
      </td>
    </tr>
  </table>
</div>
</body>
</html>
</xsl:template>

</xsl:stylesheet>
