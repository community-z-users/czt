package net.sourceforge.czt.zml2html.testing.clients.webclient;


/**
 * Representation of an HTML frame.
 */
public class Frame
{
    private String name;
    private String handlerPage;

    public Frame(String name, String handlerPage)
    {
	this.name = name;
	this.handlerPage = handlerPage;
    }

    public Link getLink()
    {
	Link l = new Link(handlerPage);
	l.setTargetFrameName(name);
	return l;
    }
}
