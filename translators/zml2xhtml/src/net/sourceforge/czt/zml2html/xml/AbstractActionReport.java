package net.sourceforge.czt.zml2html.xml;

import java.util.List;
import java.util.ArrayList;

/**
 * Abstract implentation of ActionReport interface.
 *
 * The base implementation for ActionReport objects
 * adds a pluggable java.util.List instance
 * for saving ActionMessage objects, as well
 * as facade methods for accessing the List.
 *
 * <b>Note:</b> The default List implementation for storing
 * ActionMessage instances is java.util.ArrayList.
 */
public abstract class AbstractActionReport implements ActionReport
{
    /* Description of the action that is being recorded */
    private String description;

    /* Store of ActionMessage objects associated with the ActionReport */
    private List messages;

    /**
     * Creates a named ActionReport using the default List implementation.
     * 
     * The default List implementation for storing
     * ActionMessage instances is java.util.ArrayList.
     */
    public AbstractActionReport(String description)
    {
	this(description, new ArrayList());	
    }

    /**
     * Creates a named ActionReport using the passed
     * <code>actionMessageStore</code> as the java.util.List
     * implementation to store ActionMessage instances.
     */
    public AbstractActionReport(String description, List actionMessageStore)
    {
	this.description = description;	
	setMessageContainer(actionMessageStore);
    }

    /**
     * Gives a short description of this ActionReport.
     *
     * @return short description of this ActionReport.
     */
    public String getDescription()
    {
	return this.description;
    }

    /**
     * Adds an ActionMessage to this ActionReport
     *
     * @param message message to be added
     */
    public void add(ActionMessage message)
    {
	this.messages.add(message);
    }

    /**
     * Sets the implementation List object for storing messages.
     *
     * @param messageContainer An instance of java.util.List
     *   where instance.size() == 0.
     */
    public void setMessageContainer(List messageContainer)
    {
	this.messages = messageContainer;
    }

    /**
     * Returns the java.util.List of ActionMessages recorded in 
     * this ActionReport.
     *
     * @return The ActionMessages recorded in this ActionReport.
     */
    public List getMessages()
    {
	return this.messages;
    }
   
}


