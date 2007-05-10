package net.sourceforge.czt.zml2html.xml;

import javax.xml.transform.TransformerFactory;
import javax.xml.transform.Templates;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.dom.DOMResult;
import javax.xml.transform.stream.StreamSource;
import javax.xml.transform.Source;
import javax.xml.transform.URIResolver;

import java.io.IOException;
import java.io.File;

import org.w3c.dom.Document;

/**
 * A Transformer that uses XSLT technology to transform documents.
 *
 * - only one transformation at a time
 * - one TransformActionListener
 * 
 */
public class XSLTTransformer extends SmartDocument implements net.sourceforge.czt.zml2html.xml.Transformer
{
    private TransformActionListener transformActionListener;
    private InputSource stylesheet = null;
    private Templates stylesheetTemplates = null;
    private javax.xml.transform.Transformer transformer;
    private TransformerFactory factory = null;
    private URIResolver uriResolver = null;


    /**
     * Creates a new XSLTTransformer based on the stylesheet <code>stylesheet</code>.
     *
     * @param stylesheet The source stylesheet
     *
     */
    public XSLTTransformer(InputSource stylesheet)
	throws XMLException, IOException
    {
 	super(stylesheet); // this parses the stylesheet into a DOM
 
	this.factory = TransformerFactory.newInstance();
	this.uriResolver = new URIResolverImpl(this);	
	this.transformActionListener = new TransformActionListener(this);
	this.factory.setURIResolver(uriResolver);

	//	System.out.println("URIResolverImpl registered with TransformerFactory.");

	// The stylesheet could be processed in the constructor
	// instead of the time of first use.
	//
	// try {
	//     this.stylesheetTemplates = createTemplates(stylesheet);
	// } catch(TransformerConfigurationException tce) {
	// }
    }

    /**
     * Creates a preprocessed version of the stylesheet.
     *
     * @param source The stylesheet to based the preprocessed version on.
     */
    private Templates createTemplates(Source stylesheet)
	throws TransformerConfigurationException
    {
	return factory.newTemplates(stylesheet);
    }

    /**
     * Retrieves the JAXP Transformer associated with this instance,
     * and tries to create it if it doesn't already exist.
     */
    private javax.xml.transform.Transformer getTransformer()
	throws TransformerException
    {
	if (this.transformer == null) {

	    if (this.stylesheetTemplates == null) {
		try {
		    Templates t = createTemplates(new StreamSource(this.inputSource.getInputReader()));
		    this.stylesheetTemplates = t;
		} catch (TransformerConfigurationException tce) {
		    throw new TransformerException("Error creating templates", tce);
		} catch (IOException ioe) {
		    throw new TransformerException("IO Error creating templates", ioe);
		}
	    }	    

	    try {
		javax.xml.transform.Transformer newTransformer = createTransformerFromTemplates();
		this.transformer = newTransformer;
	    } catch(TransformerConfigurationException tce) {
		throw new TransformerException("could not create a transformer. ", tce);
	    }

	}
	return this.transformer;	    
    }

    /**
     * Creates a new JAXP Transformer object for the stylesheet
     * represented by this SmartDocument.
     *
     * @throws TransformerConfigurationException 
     * 
     */
    private javax.xml.transform.Transformer createTransformerFromTemplates()
	throws TransformerConfigurationException
    {
	return stylesheetTemplates.newTransformer();
    }

    /**
     * Returns the name of the base (directory) of the stylesheet on which this
     * Transformer is based.
     *
     * @throws TransformerException the transformer doesn't know its context
     */
    public String getBase()
	throws TransformerException
    {
	try {
	    return inputSource.getBase();
	} catch (ResourceUnavailableException rue) {
	    throw new TransformerException("Transformer doesn't know its stylesheet's base address", rue);
	}
    }

    /**
     * Returns the file on which this
     * Transformer is based.
     *
     * @throws TransformerException the transformer doesn't know its context
     */
    public File getFile()
	throws TransformerException
    {
	try {
	    return this.inputSource.getFile();
	} catch (ResourceUnavailableException rue) {
	    throw new TransformerException("Transformer doesn't know anything about its context");
	}
    }

    public synchronized Document transform(Document inputDocument)
	throws TransformerException
    {
	return transform(inputDocument, this.transformActionListener);
    }    

    /**
     * Transforms a SmartDocument and reports events
     * to <code>actionReport</code>.
     *
     * @param input
     * @param actionReport
     *
     * @throws TransformerException
     *
     */
    public synchronized Document transform(Document inputDocument, TransformActionListener transformActionListener)
	throws TransformerException
    {
	if (inputDocument == null)
	    System.out.println("inputDocument is null");
	//	if (transformActionListener == null)
	//  System.out.println("transformActionListener is null");



	javax.xml.transform.Transformer transformer = getTransformer();
	Document resultDocument = null;
	DOMResult domResult = new DOMResult();
	try {
	    transformer.transform(new DOMSource(inputDocument), domResult);
	} catch (javax.xml.transform.TransformerException te) {
	    throw new net.sourceforge.czt.zml2html.xml.TransformerException(te);
	}
	return (Document)domResult.getNode();
    }

    public TransformActionReport getTransformActionReport()
    {
	return null;
    }

    public String getTransformerInfo()
    {
	return toString();
    }

    public String toString()
    {
	return "XSLT Transformer";
    }


}
