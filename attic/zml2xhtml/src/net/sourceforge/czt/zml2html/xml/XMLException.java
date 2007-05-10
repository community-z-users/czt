package net.sourceforge.czt.zml2html.xml;

/**
 * An XMLException is a general XML related error in the SmartDocument framework.
 */
public class XMLException extends Exception
{
    public XMLException(String msg)
    {
	super(msg);
    }
    public XMLException(String msg, Throwable cause)
    {
	super(msg, cause);
    }
    public XMLException(Throwable cause)
    {
	super(cause);
    }
}
