package net.sourceforge.czt.zml2html.testing.clients.webclient;

import javax.servlet.*;
import javax.servlet.http.*;

import java.io.PrintWriter;
import java.io.IOException;

import java.util.Map;
import java.util.HashMap;

/**
 * Representation of an HTML frame.
 */
public class FramesetServlet extends HttpServlet
{
    private ServletContext context;

    public FramesetServlet()
    {	
    }

    public String getHandlerPath(String servletMapping) {
	//	String contextName = context.getServletContextName();
	//      System.out.println(contextName);
	//	String prefix = contextName + "/" + servletMapping;
	//	System.out.println("/"+servletMapping);
	return servletMapping;

	//	return prefix;
    }

    public void init(ServletConfig config)
	throws ServletException
    {
	super.init(config);
	this.context = config.getServletContext();

	System.setProperty("javax.xml.transform.TransformerFactory", "org.apache.xalan.processor.TransformerFactoryImpl");

	Frame navFrame = new Frame("navigation", getHandlerPath("c"));
	Frame transformationResultFrame = new Frame("transformationresult", getHandlerPath("c"));
	Frame commentFrame = new Frame("comments", getHandlerPath("c"));
	Frame sourceFrame = new Frame("source", getHandlerPath("c"));

	Map frames = new HashMap();
	frames.put("navigation", navFrame);
	frames.put("transformationresult", transformationResultFrame);
	frames.put("comments", commentFrame);
	frames.put("source", sourceFrame);
	   
	context.setAttribute("frames",frames);
    }

    public void service(HttpServletRequest req, HttpServletResponse res)
    {
	try {
	    PrintWriter pw = res.getWriter();
	    StringBuffer fs = new StringBuffer();

	    fs.append("<frameset rows='50%,50%'>");
	    fs.append("  <frame name='navigation' src='"+getHandlerPath("c")+"?action=navigation'>");
	    fs.append("  <frameset cols='33%,34%,33%'");
	    fs.append("    <frame name='transformationresult' src=''>");
	    fs.append("    <frame name='comments' src=''>");
	    fs.append("    <frame name='source' src=''>");
	    fs.append("  </frameset>");
	    fs.append("</frameset>");

	    pw.println(fs.toString());
	} catch (IOException ioe) {
	    ioe.printStackTrace();
	}
    }
    
}
