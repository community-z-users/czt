package net.sourceforge.czt.zml2html.testing.clients.webclient;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;


/**
 * Representation of an HTML link that may cause multiple
 * frames to be refreshed.
 */
public class Link
{    
    /** User-visible portion of the hyperlink; i.e. what the user will click on */
    private String caption;

    /** Path to the page/script/servlet that will handle the link's request */
    private String handlerPage;

    /** Frame on which this link is to be loaded */
    private String targetFrameName;

    /** Collection of links to other frames that will be updated when this link is selected */
    private ArrayList frameLinks;

    /** Collection of parameters for this link */
    private HashMap params;

    /** The <code>ListOfLinks</code> to which this link belongs */
    public ListOfLinks myList;
    

    public Link()
    {
	this.frameLinks = new ArrayList();
	this.params = new HashMap();
    }

    public Link(String handlerPage)
    {
	this();
	this.caption = caption;
	this.handlerPage = handlerPage;
    }

    public void setCaption(String caption)
    {
	this.caption = caption;
    }

    public void setTargetFrameName(String frameName)
    {
	this.targetFrameName = frameName;
    }

    public void addParam(String att, String val)
    {
	params.put(att, val);
    }

    public void removeParam(String att)
    {
	params.remove(att);
    }

    public void addLink(Link link)
    {
	frameLinks.add(link);
    }

    public void setOwningList(ListOfLinks list)
    {
	Iterator i = frameLinks.iterator();
	while (i.hasNext()) {
	    Link l = (Link)i.next();
	    l.setOwningList(list);
	}
	this.myList = list;
    }

    public String getTargetFrameName()
    {
	return this.targetFrameName;
    }

    /**
     * Returns the URL to which this link is pointing.
     * 
     * <p/>If <code>linkPosition != -1</code>, then a parameter
     * <code>priority</code> will be attached to the URL with the
     * value of <code>linkPriority</code>.
     */
    public String getLinkUrl(int linkPriority)
    {
	if (linkPriority != -1)
	    addParam("priority", ""+linkPriority);

	if (handlerPage == null || handlerPage.equals(""))
	    return "";       

	StringBuffer linkUrl = new StringBuffer();
	linkUrl.append(handlerPage);

	int attCount = 0;
	Iterator paramIter = params.keySet().iterator();
	while (paramIter.hasNext()) {
	    String att = (String)paramIter.next();
	    String val = (String)params.get(att);
	    String delimitor = attCount++ == 0 ? "?" : "&";
	    
	    linkUrl.append(delimitor+att+"="+val);
	}
	
	removeParam("priority");

	return linkUrl.toString();
    }

    /**
     * Returns the complete link, with all other links associated
     * to it.
     */
    public String getHtmlLink()
    {
	StringBuffer link = new StringBuffer();
	String onclickValue = getOnclickValue(2);
	link.append("<a href='");
	link.append(getLinkUrl(1));
	link.append("' onclick=\""+onclickValue+"\">"+caption+"</a>");
	return link.toString();
    }

    private String getJavascriptFunctionName()
    {
	return myList.getJavascriptFunctionName();
    }

    /**
     * Returns the value of the <code>onClick</code> attribute
     * of the <code>a</code> (anchor) link.
     *
     * Each <code>Link</code> that has been associated with this
     * <code>Link</code> will be caused to be loaded into
     * a named frame with a JavaScript function.
     *
     * @param firstPriority 
     */
    private String getOnclickValue(int firstPriority)
    {
	StringBuffer ocValue = new StringBuffer();
	ocValue.append(getJavascriptFunctionName()+"(");
	Iterator framelinkIter = frameLinks.iterator();
	while (framelinkIter.hasNext()) {
	    Link link = (Link)framelinkIter.next();
	    ocValue.append("'"+link.getLinkUrl(firstPriority++)+"'");
	    if (framelinkIter.hasNext())
		ocValue.append(",");
	}

	ocValue.append(")");
	return ocValue.toString();
    }

    public static void main(String args[])
    {
	Link l = new Link("/gerret/gerret.jsp");
	l.setCaption("gerret");
	Link frame1Link = new Link("/evan/evan.jsp");
	frame1Link.setCaption("evan");
	l.addLink(frame1Link);
	System.out.println(l.getHtmlLink());

	System.out.println();

        l = new Link("/gerret/gerret.jsp");
	l.setCaption("gerret");
	Frame f1 = new Frame("NAV", "/nav/nav.jsp");
	Link f1link1 = f1.getLink();
	l.addLink(f1link1);
	Frame f2 = new Frame("output", "/output/output.jsp");
	Link f1link2 = f2.getLink();
	l.addLink(f1link2);

	//	System.out.println(l.getJavascriptFrameloadingFunction());

	System.out.println(l.getHtmlLink());
    }

}
