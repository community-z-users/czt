package net.sourceforge.czt.zml2html.xml;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.ParserConfigurationException;
import java.util.Date;

/**
 * A pool of javax.xml.parsers.DocumentBuilder parsers.
 *
 * A <code>ParserPool</code> is associated with a JAXP DocumentBuilderFactory
 * that produces new instances for the pool.
 *
 * @author Gerret Apelt
 *
 */
public class ParserPool extends ObjectPool
{
    /* Factory for creating new instances */
    private DocumentBuilderFactory factory = null;
    
    /**
     * Create a new Parser Pool for parsers created by
     * <code>factory</code>.
     *
     * @param factory Factory for creating new parser instances
     * @param id Unique ID of this pool
     */
    public ParserPool(DocumentBuilderFactory factory, String id)
    {
	super(id);	
	this.factory = factory;
    }

    /**
     * Create a new <code>Object</code> instance to be put in the pool 
     * (implementation of abstract superclass method).
     *
     * <b>Note:</c>A new Parser is returned by this method,
     * but it is not added to the pool.
     *
     * @throws IndexOutOfBoundsException if the pool is full
     * @throws XMLException if there was an error creating the instance
     */
    protected Object newInstance()
	throws IndexOutOfBoundsException, XMLException
    {
	bailIfFull();

	DocumentBuilder builder = null;

	try {
	    builder = factory.newDocumentBuilder();
	} catch (ParserConfigurationException pce) {
	    throw new XMLException("Could not create parser", pce);
	}

	return builder;
    }

    /**
     * Copnvenience methods that retrieves a DocumentBuilder instance from the pool.
     *
     * This method will block until an instance could be delivered.
     *
     */
    public DocumentBuilder getParserInstance()
    {
	return (DocumentBuilder)getInstance();
    }

    /**
     * Returns the factory associated with this ParserPool.
     */
    public DocumentBuilderFactory getFactory()
    {
	return this.factory;
    }
	
}

