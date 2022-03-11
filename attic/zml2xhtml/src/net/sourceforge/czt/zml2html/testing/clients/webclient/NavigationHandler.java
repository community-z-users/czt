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

public class NavigationHandler    
{   
    private Testset root;
    private Testset testset;
    private Map frames;

    public NavigationHandler(Testset rootTestset, Map frames)
    {
	root = rootTestset;
	this.frames = frames;
    }

    public void service(HttpServletRequest req, HttpServletResponse res)
	throws ServletException
    {
	PrintWriter pw;
	try {
	    pw = res.getWriter();
	} catch(IOException ioe) {
	    throw new ServletException(ioe);
	}

	String testsetName = (String)req.getParameter("testset");
	if (testsetName == null)
	    testsetName = "testcases";
	
	testset = root.getTestset(testsetName);

	ListOfLinks listOfAncestorLinks = getAncestorLinks(testsetName);
	ListOfLinks listOfTestsetLinks = getTestsetLinks(testsetName);
	ListOfLinks listOfTestcaseLinks = getTestcaseLinks(testsetName);

	Iterator ancestorLinks = listOfAncestorLinks.iterator();
	Iterator testsetLinks = listOfTestsetLinks.iterator();
	Iterator testcaseLinks = listOfTestcaseLinks.iterator();

	pw.println("<HTML><HEAD>");
	pw.println(listOfTestcaseLinks.getJavascriptFrameloadingFunction());
	pw.println("</HEAD><BODY>");
       
	pw.println("<h2>Ancestors</h2>");
	while (ancestorLinks.hasNext()) {
	    Link l = (Link)ancestorLinks.next();
	    pw.println(l.getHtmlLink());
	    if (ancestorLinks.hasNext()) {
		pw.println(":");
	    }
	}
	
	pw.println("<h2>Testsets</h2>");
	if (!testsetLinks.hasNext()) {
	    pw.println("There are no testsets at this level<br/>");
	}
	while (testsetLinks.hasNext()) {
	    Link l = (Link)testsetLinks.next();
	    pw.println(l.getHtmlLink()+"<br/>");
	}
    
	pw.println("<h2>Testcases</h2>");
	if (!testcaseLinks.hasNext()) {
	    pw.println("There are no testcases at this level<br/>");
	}
	while (testcaseLinks.hasNext()) {
	    Link l = (Link)testcaseLinks.next();
	    pw.println(l.getHtmlLink()+"<br/>");
	}

	pw.println("</BODY></HTML>");
	
    }

    private ListOfLinks getAncestorLinks(String testsetName)
    {
	Iterator i = testset.getAncestorsIterator();
	ListOfLinks listOfLinks = new ListOfLinks();
	while (i.hasNext()) {
	    Testset testset = (Testset)i.next();
	    Link l = ((Frame)frames.get("navigation")).getLink();
	    l.setCaption(testset.getName());
	    l.addParam("testset", testset.getQualifiedName());
	    l.addParam("action", "navigation");
	    listOfLinks.addLink(l);
	}
	return listOfLinks;
    }

    private ListOfLinks getTestsetLinks(String testsetName)
    {
	Iterator i = testset.getTestsets();
	ListOfLinks listOfLinks = new ListOfLinks();
	while (i.hasNext()) {
	    Testset testset = (Testset)i.next();
	    Link l = ((Frame)frames.get("navigation")).getLink();
	    l.setCaption(testset.getName());
	    l.addParam("testset", testset.getQualifiedName());
	    l.addParam("action", "navigation");
	    listOfLinks.addLink(l);
	}
	return listOfLinks;
    }

    private ListOfLinks getTestcaseLinks(String testsetName)
    {
	Iterator i = testset.getTestcases();

	ArrayList frameNames = new ArrayList();
	frameNames.add("source");
	frameNames.add("transformationresult");
	ListOfLinks listOfLinks = new ListOfLinks(frameNames);

	while (i.hasNext()) {
	    Testcase testcase = (Testcase)i.next();
	    Link l = new Link("");
	    l.setCaption(testcase.getName());
	    l.addParam("testcase", testcase.getName());
	    l.addParam("action", "navigation");

	    Link sourceLink = ((Frame)frames.get("source")).getLink();
	    sourceLink.addParam("action", "source");
	    sourceLink.addParam("testcase", testcase.getQualifiedName());
	    l.addLink(sourceLink);

	    Link transformResultLink = ((Frame)frames.get("transformationresult")).getLink();
	    transformResultLink.addParam("action", "transformationresult");
	    transformResultLink.addParam("testcase", testcase.getQualifiedName());
	    l.addLink(transformResultLink);

	    listOfLinks.addLink(l);
	}

	return listOfLinks;
    }
}
