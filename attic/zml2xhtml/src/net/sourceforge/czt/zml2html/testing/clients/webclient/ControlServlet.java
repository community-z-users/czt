package net.sourceforge.czt.zml2html.testing.clients.webclient;

import javax.servlet.*;
import javax.servlet.http.*;

import java.io.PrintWriter;
import java.io.IOException;
import java.io.File;

import java.util.Map;

import net.sourceforge.czt.zml2html.testing.Testset;

/**
 * Representation of an HTML frame.
 */
public class ControlServlet extends HttpServlet
{
    private ServletContext context;

    private Testset rootTestset;

    public ControlServlet()
    {	
    }

    public void init(ServletConfig config)
	throws ServletException
    {
	this.context = config.getServletContext();

	String path = context.getInitParameter("testcases-directory");

	File dir = new File(path);
	rootTestset = new Testset(true, null, dir);
	rootTestset.populate(true);
    }

    public void service(HttpServletRequest req, HttpServletResponse res)
	throws ServletException
    {
	String action = req.getParameter("action");
	String requestSetId = req.getParameter("reqsetid");
	String priority = req.getParameter("priority");	

	if (action == null)
	    throw new ServletException("no action parameter has been specified");

	Testset rootTestset = getRootTestset(requestSetId, priority);
	Map frames = (Map)context.getAttribute("frames");

	if (action.equals("navigation")) {
	    NavigationHandler handler = new NavigationHandler(rootTestset, frames);
	    handler.service(req, res);
	} else if (action.equals("source") || action.equals("transformationresult")) {
	    DisplayHandler handler = new DisplayHandler(rootTestset, frames);
	    handler.service(req, res);
	} else {
	    throw new ServletException("'"+action+"' is not a valid action.");
	}

	/*
	try {
	    String jspFile = (String)req.getAttribute("jsppage");
	    RequestDispatcher rd = req.getRequestDispatcher("/"+jspFile);
	    rd.forward(req, res);	
	} catch(IOException ioe) {
	    throw new ServletException(ioe);
	}
	*/

    }

    private Testset getRootTestset(String requestSetId, String priority)
    {
	Testset rootTestset = this.rootTestset;

	if (priority == null)
	    return rootTestset;
	else
	    return rootTestset;
    }
    
}
