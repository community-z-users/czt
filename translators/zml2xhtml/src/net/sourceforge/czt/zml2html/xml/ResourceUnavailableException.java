package net.sourceforge.czt.zml2html.xml;

/**
 * Thrown when an ObjectPool is unable to service a request for 
 * a Reusable component.
 *
 */
public class ResourceUnavailableException extends RuntimeException
{
    public ResourceUnavailableException(String msg)
    {
	super(msg);
    }

    public ResourceUnavailableException(String msg, Exception cause)
    {
	super(msg, cause);
    }

    public ResourceUnavailableException(Throwable cause)
    {
	super(cause);
    }
}
