package net.sourceforge.czt.zml2html.testing.clients.webclient;

import javax.servlet.*;
import javax.servlet.http.*;

import java.io.PrintWriter;
import java.io.IOException;

/**
 * Representation of an HTML frame.
 */
public class ClientServlet extends HttpServlet
{
    private ServletContext context;
    private static String servletPath = null;

    public ClientServlet()
    {	
    }

    public String getPrefix() {
	String contextName = context.getServletContextName();
	String prefix = contextName + servletPath;
	return prefix;
    }

    public void init(ServletConfig config)
	throws ServletException
    {
	super.init(config);
	this.context = config.getServletContext();
    }

    public void service(HttpServletRequest req, HttpServletResponse res)
    {
	if (servletPath == null) {
	    servletPath = req.getServletPath();
	}

	try {
	    PrintWriter pw = res.getWriter();

	    pw.println(getPrefix());
	} catch (IOException ioe) {
	    ioe.printStackTrace();
	}
    }
    
}
