package net.sourceforge.czt.zml2html.xml;

import java.util.Date;

/**
 * A message recorded during an action.
 */
public class ActionMessage
{
    /* Severity level; typically "warning", "error" or "fatal error" */
    public String level;

    /* Date of Creation of this ActionMessage */
    public Date date;
    
    /* Mesasage text */
    public String message;

    /* Base Exception */
    public Exception cause;

    /**
     * Creates a new ActionMessage.
     *
     * @param level Severity level of the message
     * @param message Mesage text
     * @param cause Exception that caused this message, or <code>null</code> if there was no Exception.
     */
    public ActionMessage(String level, String message, Exception cause)
    {
	this.level = level;
	this.message = message;
	this.date = new Date();
	this.cause = cause;
    }

    /**
     * String representation of this message
     */
    public String toString()
    {
	return level+": "+message;
    }
}
