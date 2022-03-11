package net.sourceforge.czt.zml2html.xml;

/**
 * A (typically wrapped) exception that occurred during Validation.
 */
public class TransformerException extends Exception
{
    public TransformerException(String msg)
    {
	super(msg);
    }
    public TransformerException(String msg, Throwable cause)
    {
	super(msg, cause);
    }
    public TransformerException(Throwable cause)
    {
	super(cause);
    }
}
