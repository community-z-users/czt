package net.sourceforge.czt.zml2html.xml;

import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

/**
 * Listens to parsing events from a SmartDocument
 * (by implementing org.xml.sax.ErrorHandler) and produces
 * ActionReport objects based on the callbacks received.
 */
public class ParseActionListener extends AbstractActionListener implements ErrorHandler
{
    /* Document being parsed */
    private SmartDocument sourceDocument;

    private int errorCount = 0;
    
    /**
     * Create a new ParseActionListener
     */
    public ParseActionListener(SmartDocument sourceDocument)
    {
	super();
	this.sourceDocument = sourceDocument;
    }

    /**
     * Alert this instance that an action is starting.
     */
    public void startAction(String description)
	throws IllegalStateException
    {
	super.startAction(description);
	curActionReport = new GenericActionReport(description);
    }

    /*
     *
     * Implementation of org.xml.sax.ErrorHandler
     *
     */

    /**
     * Error
     */
    public void error(SAXParseException spe)
	throws SAXException
    {
	ensureValidState(ACTION_IN_PROGRESS);
	this.errorCount++;
	ActionMessage message = new ActionMessage("error", spe.getMessage(), spe);
	curActionReport.add(message);
    }
    
    /**
     * Warning
     */
    public void warning(SAXParseException spe)
	throws SAXException
    {
	System.out.println("helloxx");
	ensureValidState(ACTION_IN_PROGRESS);
	ActionMessage message = new ActionMessage("warning", spe.getMessage(), spe);
	curActionReport.add(message);
    }

    /**
     * Fatal Error
     */ 
    public void fatalError(SAXParseException spe)
	throws SAXException
    {
	ensureValidState(ACTION_IN_PROGRESS);
	this.errorCount++;
	ActionMessage message = new ActionMessage("fatalError", spe.getMessage(), spe);
	curActionReport.add(message);
    }

    public int getErrorCount()
    {
	return this.errorCount;
    }
}





