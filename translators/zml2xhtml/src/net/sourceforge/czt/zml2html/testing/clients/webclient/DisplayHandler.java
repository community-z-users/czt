package net.sourceforge.czt.zml2html.testing.clients.webclient;

import java.io.PrintWriter;
import java.io.IOException;

import javax.servlet.*;
import javax.servlet.http.*;

import java.util.Iterator;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.zml2html.testing.Testset;
import net.sourceforge.czt.zml2html.testing.Testcase;
import net.sourceforge.czt.zml2html.xml.XHTMLDocument;
import net.sourceforge.czt.zml2html.xml.XMLException;
import net.sourceforge.czt.zml2html.xml.TransformerException;

public class DisplayHandler
{   
    private Testset root;
    private Testset testset;
    private Map frames;

    public DisplayHandler(Testset rootTestset, Map frames)
    {
	root = rootTestset;
	this.frames = frames;
    }

    public void service(HttpServletRequest req, HttpServletResponse res)
	throws ServletException
    {
	try {
	    PrintWriter pw = res.getWriter();

	    String testcaseName = (String)req.getParameter("testcase");
	    if (testcaseName == null)
		throw new ServletException("invalid testcase name: '"+testcaseName+"'");
	    Testcase testcase = root.getTestcase(testcaseName);

	    String action = (String)req.getParameter("action");
	    
	    if (action.equals("transformationresult")) {
		res.setContentType("text/html");
		try {
		    XHTMLDocument xhtmlDoc = testcase.getTestcaseDoc().transformToXHTML();
		    pw.println(xhtmlDoc.getXMLAsString());		    
		} catch (TransformerException te) {
		    throw new ServletException(te);
		} catch (XMLException xmle) {
		    throw new ServletException(xmle);
		}
	    } else if (action.equals("source")) {
		res.setContentType("text/xml");
		try {
		    pw.println(testcase.getTestcaseDoc().getXMLAsString());
		} catch (XMLException xmle) {
		    throw new ServletException(xmle);
		}
	    }

	} catch(IOException ioe) {
	    throw new ServletException(ioe);
	}

	req.setAttribute("jsppage", "navigation.jsp");
    }

}
