<?xml version="1.0" encoding="utf-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
                version="1.0">

  <xsl:output method="html"/>

  <xsl:template match="/">
    <html>
      <head>
        <title>FAQ</title>
        <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1"/>
      </head>
      <body bgcolor="#FFFFFF">
        <xsl:apply-templates/>
      </body>
    </html>
  </xsl:template>

  <xsl:template match="faq">
    <h2><xsl:value-of select="question"/></h2>
    <xsl:for-each select="answer/* | anser/text()">
      <xsl:copy-of select="."/>
    </xsl:for-each>
  </xsl:template>

</xsl:stylesheet>
