<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0"
  xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<!-- This XSLT stylesheet adds a CZT header and left-hand sidebar
     onto a page of html content.  The input page should be in
     XML format, but typically consists mostly of raw HTML inside
     a CDATA string.

     If the 'pagename' variable matches one of the links in the sidebar,
     then that link is highlighted with an arrow rather than a bullet, to
     indicate it is the current page.  
--> 

<xsl:output method="text" encoding="UTF-8" indent="yes"/>

<xsl:param name="pagename" select="'Home'"/>

<xsl:variable name="lowercase" select="'abcdefghijklmnopqrstuvwxyz'"/>
<xsl:variable name="uppercase" select="'ABCDEFGHIJKLMNOPQRSTUVWXYZ'"/>

<xsl:template name="toclink">
  <xsl:param name="name"/>
  <xsl:param name="url"/>
  <xsl:variable name="lowername"
      select="translate($name,$uppercase,$lowercase)"/>
  <xsl:choose>
    <xsl:when test="$pagename=$lowername">
      <xsl:text><![CDATA[<img border="0" alt="--&gt; " src="images/arrow.gif" width="20" height="15"/>]]></xsl:text>
    </xsl:when>
    <xsl:otherwise>
      <xsl:text><![CDATA[<img border="0" alt="* " src="images/bullet.gif" width="16" height="12">]]></xsl:text>
    </xsl:otherwise>
  </xsl:choose>
  <xsl:text><![CDATA[<a href="]]></xsl:text>
  <xsl:value-of select="$url"/>
  <xsl:text><![CDATA[">]]></xsl:text>
  <xsl:value-of select="$name"/>
  <xsl:text><![CDATA[</a><p/>
]]></xsl:text>
</xsl:template>

<xsl:template match="/content">
  <xsl:text><![CDATA[<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN"
    "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
  <title>CZT ]]></xsl:text><xsl:value-of select="$pagename"/><xsl:text><![CDATA[</title>
  <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
  <meta http-equiv="Content-Language" content="en-us">
  <meta http-equiv="Author" content="Mark Utting">
</head>

<body bgcolor="#87a7ff" link="#1c32ff" vlink="#0d1777" alink="#FF0000">

<div align="left">
  <table border="0" cellpadding="10" cellspacing="0" width="100%">
    <tr>

      <td align="right" valign="top" width="15%" height="150">
        <img border="0" alt="CZT logo" src="images/cztlogo150.jpg" width="150" height="150"></td>
      <td valign="bottom" height="150">
        <img border="0" alt="CZT: Community Z Tools" src="images/czttitle150.jpg" height="150">
      </td>
    </tr>
    <tr>
      <td valign="top" width="15%">
        <p/>
        ]]></xsl:text>
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
          <xsl:with-param name="url" select="'news.html'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'People'"/>
          <xsl:with-param name="url" select="'people.html'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'Screenshots'"/>
          <xsl:with-param name="url" select="'screenshots.html'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'Documentation'"/>
          <xsl:with-param name="url" select="'documentation.html'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'Development'"/>
          <xsl:with-param name="url" select="'http://sourceforge.net/projects/czt'"/>
        </xsl:call-template>
        <xsl:call-template name="toclink">
          <xsl:with-param name="name" select="'Downloads'"/>
          <xsl:with-param name="url" select="'http://sourceforge.net/project/showfiles.php?group_id=86250'"/>
        </xsl:call-template>
        <xsl:text><![CDATA[
      <p>
      <a href="http://sourceforge.net"><img src="http://sourceforge.net/sflogo.php?group_id=86250&amp;type=4" width="125" height="37" border="0" alt="SourceForge.net Logo" /></a>
      </td>
      <td valign="top" bgcolor="#d8d8d8"> ]]>
    </xsl:text>
  <xsl:value-of select="."/>
    <xsl:text><![CDATA[</td>
    </tr>
  </table>
</div>
</body>
</html>]]>
</xsl:text>
</xsl:template>

</xsl:stylesheet>
