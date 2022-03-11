package net.sourceforge.czt.zml2html.xml;

import org.w3c.dom.Document;

import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import java.io.StringWriter;

/**
 *
 */
public class IndentingXMLWriter extends AbstractXMLWriter
{
    Transformer transformer;
    
    /**
     * Standard Constructor.
     *
     * <b>Note:</b> Everything in the current XMLWriter
     * implementations should be refactored
     * for efficiency.
     */
    public IndentingXMLWriter()
	throws TransformerException
    {
	try {
	    TransformerFactory tFactory = TransformerFactory.newInstance();
	    this.transformer = tFactory.newTransformer();
	} catch (TransformerConfigurationException tce) {
	    throw new TransformerException(tce);
	} catch (javax.xml.transform.TransformerException te) {
	    throw new TransformerException(te);
	}
    }

    public String getSerialization(Document document)
	throws XMLException
    {
	StringWriter stringWriter = new StringWriter();
	StreamResult result = new StreamResult(stringWriter);
	DOMSource source = new DOMSource(document);
	transformer.setOutputProperty(javax.xml.transform.OutputKeys.INDENT, "yes");
	transformer.setOutputProperty(javax.xml.transform.OutputKeys.METHOD, "xml");

	try {
	    transformer.transform(source, result);
	} catch (javax.xml.transform.TransformerException te) {
	    throw new XMLException("could not serialize content", te);
	}

	return stringWriter.toString();	
    }
}




