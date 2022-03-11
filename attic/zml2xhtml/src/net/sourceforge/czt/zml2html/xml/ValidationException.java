package net.sourceforge.czt.zml2html.xml;

/**
 * A (typically wrapped) exception that occurred during Validation.
 */
public class ValidationException extends Exception
{
    public ValidationException(String msg)
    {
	super(msg);
    }
    public ValidationException(String msg, Throwable cause)
    {
	super(msg, cause);
    }
    public ValidationException(Throwable cause)
    {
	super(cause);
    }
}
