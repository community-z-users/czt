This is the CZT (czt.sourceforge.net) ZML2HTML subproject. 

ZML2HTML provides a set of XSLT 1.1 stylesheets that define
the transformation from ZML-held specifications to XHTML.

(I) Subproject Files

README.txt		this file
build.xml		ANT build file
src			java source code
testcases		ZML unit test specs
xsl			the ZML2HTML stylesheets (pass Z.xsl to transformers)
zml2html.testing.xsd	W3C schema for http://czt.sourceforge.net/zml/zml2html/testing namespace
zstyle.css		CSS stylesheet use by generated XHTML


(II) Testing Framework
A Java testing framework is provided to aid in verifying that the stylesheets'
output properly resembles ISO Z notation.
There are two interfaces to the testing classes: a Command Line Interface for
regression testing, and a Web Interface for ineractive testing, commenting,
approval/disapproval of testcases, etc.

To invoke the CLI interface:
   java net.sourceforge.czt.zml2html.testing.clients.cmdlineclient.CmdlineClient

The web interface is a J2EE web application and requires a Servlet Container, such
as Caucho Resin (http://www.caucho.com) or Jakarta Tomcat
(http://jakarta.apache.org/tomcat/), to be deployed. 

Here's an example for how to deploy ZML2HTML's web testing interface, using
Caucho Resin as the Servlet Container.

       1) Download and expand Resin.
          We will assume that you installed Resin in $RESIN_HOME.

       2) Instruct ZML2HTML's build.xml as to the whereabouts
          of Resin's "hotdeploy" directory. You do this by
	  setting the property "servletcontainer.deploy.dir"
	  to "$RESIN_HOME/webapps".

       3) The testing framework has three dependencies:
            - servlet API 2.4
	    - a JAXP Schema-Validating parser (such as xerces)
	    - the Xalan transformation engine

	  The corresponding .jar libraries are defined in
	  $CZT_HOME/czt.properties. You need to ensure they are
	  available also to the servlet container for deployment.

	  The easiest way to accomplish this is by putting them
	  on the system classpath.

       3) Deploy the web application to Resin -- run

             ant deploy

       4) Start Resin: $RESIN_HOME/bin/httpd.sh

You should now be able to access the testing web interface at
http://localhost:8080/zml2html_testing/frameset.