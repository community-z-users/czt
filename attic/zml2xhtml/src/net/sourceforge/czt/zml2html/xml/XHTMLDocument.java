package net.sourceforge.czt.zml2html.xml;

import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;

import java.io.File;
import java.io.IOException;


/**
 * Abstraction of an XHTML document.
 */
public class XHTMLDocument extends EasyDocument
{
    public XHTMLDocument(String path)
	throws XMLException, IOException
    {
	this(new File(path));
    }

    public XHTMLDocument(File file)
	throws XMLException, IOException
    {
	super(file);
	PooledParserFactory ppFactory = PooledParserFactory.getSingleton();
	if (!ppFactory.hasPool("xhtml"))
	    ppFactory.addPool(getXHTMLValidatingFactory(), "xhtml");
    }

    public XHTMLDocument(Document dom)
    {
	super(dom);
    }

    public boolean isValid()
	throws ValidationException
    {
	return isValid("xhtml");
    }

    private DocumentBuilderFactory getXHTMLValidatingFactory()
    {
	final String JAXP_SCHEMA_LANGUAGE =
	    "http://java.sun.com/xml/jaxp/properties/schemaLanguage";
	final String W3C_XML_SCHEMA =
	    "http://www.w3.org/2001/XMLSchema";
	final String JAXP_SCHEMA_LOCATION =
	    "http://apache.org/xml/properties/schema/external-schemaLocation";
	final String SCHEMA_LOCATION =
	    "http://czt.sourceforge.net/zml file:///home/ga11/development/zml/xhtml1-strict.xsd";
	
	DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
	factory.setNamespaceAware(true);
	factory.setValidating(true);
	
	try {
	    factory.setAttribute(JAXP_SCHEMA_LANGUAGE, W3C_XML_SCHEMA);
	    factory.setAttribute(JAXP_SCHEMA_LOCATION, SCHEMA_LOCATION);
	} catch(IllegalArgumentException x) {
	    x.printStackTrace();
	    throw new RuntimeException("DOM parser is not JAXP 1.2 compliant.");
	}
	
	return factory;
    }


}
