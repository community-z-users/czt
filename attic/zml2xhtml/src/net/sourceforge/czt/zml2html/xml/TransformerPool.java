package net.sourceforge.czt.zml2html.xml;

//import javax.xml.parsers.DocumentBuilderFactory;
//import javax.xml.parsers.DocumentBuilder;

import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerFactory;

/**
 * A pool of javax.xml.transform.Transformer XSLT transformers.
 *
 * Each pool is built around a factory.
 *
 */
public class TransformerPool extends ObjectPool
{
    private TransformerFactory factory = null;
    
    public TransformerPool(TransformerFactory factory, String id)
    {
	super(id);	
	this.factory = factory;
    }

    /**
     * Create a new Transformer instance to be put in the pool.
     *
     * Housekeeping on this object is taken care of in the superclass
     */
    public Object newInstance()
	throws IndexOutOfBoundsException, XMLException
    {
	bailIfFull();

	javax.xml.transform.Transformer transformer = null;

	try {
	    transformer = factory.newTransformer();
	} catch (TransformerConfigurationException tce) {
	    throw new XMLException("Could not instantiate transformer", tce);
	}

	return transformer;
    }

    /**
     *
     */
    public Transformer getTransformerInstance()
    {
	return (Transformer)getInstance();
    }
	
}

