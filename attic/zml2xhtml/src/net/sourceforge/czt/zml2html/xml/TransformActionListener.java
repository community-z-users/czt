package net.sourceforge.czt.zml2html.xml;

import javax.xml.transform.ErrorListener;
import javax.xml.transform.Transformer;

/**
 * Listens to Transformation events
 * (by implementing javax.xml.transform.ErrorListener).
 */
public class TransformActionListener extends AbstractActionListener implements ErrorListener
{
    /* Document being parsed */
    private Transformer transformer;
    
    /**
     * Create a new TransformActionListener
     */
    public TransformActionListener(net.sourceforge.czt.zml2html.xml.Transformer transfomer)
    {
	this.transformer = transformer;
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
    public void error(javax.xml.transform.TransformerException exception)
	throws javax.xml.transform.TransformerException
    {
	ensureValidState(ACTION_IN_PROGRESS);
	ActionMessage message = new ActionMessage("error", exception.getMessage(), exception);
	curActionReport.add(message);
    }
    
    /**
     * Warning
     */
    public void warning(javax.xml.transform.TransformerException exception)
	throws javax.xml.transform.TransformerException
    {
	ensureValidState(ACTION_IN_PROGRESS);
	ActionMessage message = new ActionMessage("warning", exception.getMessage(), exception);
	curActionReport.add(message);
    }

    /**
     * Fatal Error
     */ 
    public void fatalError(javax.xml.transform.TransformerException exception)
	throws javax.xml.transform.TransformerException
    {
	ensureValidState(ACTION_IN_PROGRESS);
	ActionMessage message = new ActionMessage("fatalError", exception.getMessage(), exception);
	curActionReport.add(message);
    }
}



