package net.sourceforge.czt.zml2html.testing;

import javax.xml.parsers.DocumentBuilderFactory;

import java.io.File;
import java.io.IOException;

import java.util.Iterator;

import net.sourceforge.czt.zml2html.xml.*;

import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import java.util.List;
import java.util.ArrayList;
import org.apache.xpath.*;
import org.w3c.dom.Element;
import org.w3c.dom.Document;
import org.w3c.dom.DOMException;
import java.util.Hashtable;

/**
 * Abstraction of a ZML document.
 *
 * <p><b>Note</b>: This class provides document-level
 * support for ZML files, and definitely no content-level
 * support.</p>
 *
 * <p>The ZML example: suppose you want to
 * parse, transform, and validate a ZML file
 * using this class.</p>
 *
 * <code>
 *   ZMLDocument zmlDoc = new ZMLDocument("/research/zml/specification.zml");<br/>
 *   if (zmlDoc.isValid())<br/>
 *     System.out.println("The document "+zmlDoc+" is valid");<br/>
 *   SmartDocument newDoc = zmlDoc.transform("/research/zml/Z.xsl");<br/>
 *<br/>
 *   newDoc.writer("/research/zml/changed_specifiation.xsl");<br/>
 * </code>
 *
 */
public class ZMLDocument extends EasyDocument
{
    public static final String ZML_NAMESPACE_URI = "http://czt.sourceforge.net/zml";
    public static final String ZML_ZML2HTML_TESTING_NAMESPACE_URI = "http://czt.sourceforge.net/zml/zml2html/testing";

    public CommentHashtable comments;

    // namespace node of the ZML specification; needed by Xalan's XPath implementation
    private Element namespaceNode; 
    

    private static PooledParserFactory ppFactory = PooledParserFactory.getSingleton();
    static {
	if (!ppFactory.hasPool("zml"))
	    ppFactory.addPool(getZMLFactory(), "zml");
    }

    public ZMLDocument(String path)
	throws XMLException, IOException, TransformerException
    {
	this(new File(path));
    }

    public ZMLDocument(File file)
	throws XMLException, IOException
    {
	super(file, "zml");
	namespaceNode = getNamespaceNode();	
	comments = new CommentHashtable(this);
    }

    public XHTMLDocument transformToXHTML()
	throws TransformerException
    {
	// XXX: need to pass Z.xsl as init parameter
	SmartDocument sd = transform("/home/ga11/development/zml/zml2html/xsl/Z.xsl");
	XHTMLDocument xhtmlDoc = new XHTMLDocument(sd.getDOM());
	return xhtmlDoc;
    }

    public boolean isEqual(ZMLDocument doc)
    {
	Comparator comparator = new ZMLComparator();
	return comparator.isEqual(getDOM(), doc.getDOM());
    }

    /**
     * Writes a serialization of <code>ZMLDocument</code> to disk,
     * ensuring that the comments are up to date.
     */
    public void write(File f)
	throws XMLException
    {
	try {
	    deleteCommentsFromDOM();
	    insertCommentListIntoDOM(comments.getAsElement(getDOM()));
	} catch (javax.xml.transform.TransformerException te) {
	    throw new XMLException(te);
	} catch (DOMException de) {
	    throw new XMLException(de);
	}

	super.write(f);
    }

    public int addComment(Comment comment)
    {
	return comments.add(comment);
    }

    private Element getNamespaceNode()
    {
	Element namespaceNode = getDOM().createElement("namespace");
	namespaceNode.setAttribute("xmlns:Z", ZML_NAMESPACE_URI);
	namespaceNode.setAttribute("xmlns:zml2html", ZML_ZML2HTML_TESTING_NAMESPACE_URI);
	return namespaceNode;
    }
    
    /**
     * Deletes all 'comment' nodes (from the http://czt.sourceforge.net/zml/zml2html/testing
     * namespace) in the input document DOM.
     */
    private void deleteCommentsFromDOM()
	throws javax.xml.transform.TransformerException
    {
	Node specNode= getSpecNode();
	List l = getNodesByXPath("Z:Spec/Z:Anns[zml2html:comment-list][1]");
	Iterator i = l.iterator();
	if (i.hasNext()) {
	    Node commentAnnsNode = (Node)i.next();
	    specNode.removeChild(commentAnnsNode);
	} else {
	    System.out.println("NO XPATH MATCH!");
	}
    }

    private void insertCommentListIntoDOM(Element commentListElement)
	throws javax.xml.transform.TransformerException, DOMException
    {
	Node specNode= getSpecNode();
	NodeList specChildren = specNode.getChildNodes();

	java.util.ArrayList l = new java.util.ArrayList();

	for (int i = 0; i < specChildren.getLength(); i++) {
	    Node child = specChildren.item(i);
	    l.add(child);
	    specNode.removeChild(child);
	}	
	//	System.out.println(((Element)commentListElement).getTagName());
	specNode.appendChild(commentListElement);
	
	Iterator i = l.iterator();
	while (i.hasNext()) {
	    specNode.appendChild((Node)i.next());
	}	
    }

    private Node getSpecNode()
	throws javax.xml.transform.TransformerException
    {
	List l = getNodesByXPath("Z:Spec");
	Iterator i = l.iterator();
	Node specNode= (Node)i.next();
	return specNode;
    }

    public boolean isValid()
	throws ValidationException
    {
	PooledParserFactory ppFactory = PooledParserFactory.getSingleton();
	if (!ppFactory.hasPool("validatingzml"))
	    ppFactory.addPool(ZMLDocument.getZMLValidatingFactory(), "validatingzml");	

	return isValid("validatingzml");
    }

    /**
     * Returns a factory of parsers that parses <i>and</i> validates (but doesn't validate) ZML documents.
     */
    private static DocumentBuilderFactory getZMLValidatingFactory()
    {
	final String JAXP_SCHEMA_LANGUAGE =
	    "http://java.sun.com/xml/jaxp/properties/schemaLanguage";
	final String W3C_XML_SCHEMA =
	    "http://www.w3.org/2001/XMLSchema";
	final String JAXP_SCHEMA_LOCATION =
	    "http://apache.org/xml/properties/schema/external-schemaLocation";
	final String SCHEMA_LOCATION =
	    ZML_NAMESPACE_URI+" file:///Z.xsd "+
	    ZML_ZML2HTML_TESTING_NAMESPACE_URI+" file:///zml2html.testing.xsd";
	
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

    /**
     * Returns a factory of parsers that parses (but doesn't validate) ZML documents.
     */
    private static DocumentBuilderFactory getZMLFactory()
    {
	DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
	factory.setNamespaceAware(true);
		
	return factory;
    }

    /** 
     * Returns a {@link java.util.List List} of nodes from document <i>doc</i> matchings the XPath
     * expression <i>xpathexpr</i>, where the namespace node required by Apache's XPath interface
     * is initialized to support namespaces for Z and ZMLTP.
     *
     * @param doc The DOM document in which to search for matching nodes
     * @param xpathexpr The expression that a node has to match
     *
     */
    public List getNodesByXPath(String xpathexpr)
	throws javax.xml.transform.TransformerException    
    {
	return ZMLDocument.getNodesByXPath(getDOM(), xpathexpr, this.namespaceNode);
    }

    /**
     *
     * Returns a {@link java.util.List} of nodes from document <i>doc</i> matching the XPath
     * expression <i>xpathexpr</i>.
     *
     * @param doc The DOM document in which to search for matching nodes
     * @param xpathexpr The expression that a node has to match
     * @param namespacenode A namespace node to be supplied to Apache's XPath engine
     * 
     * @throws TransformerException
     */
    public static List getNodesByXPath(Document doc, String xpathexpr, Element namespacenode)
	throws javax.xml.transform.TransformerException 
    {	
	NodeList nl = XPathAPI.selectNodeList(doc, xpathexpr, namespacenode);
	List l = new ArrayList();
	for (int i = 0; i < nl.getLength(); i++) {
	    l.add(nl.item(i));
	}
	return l;
    }

    /**
     * Returns the concattenation of an Elements text child nodes
     * as a String.
     */
    public static String getElementText(Element e)
    {
	String text = "";
	NodeList nl = e.getChildNodes();
	for (int i = 0; i < nl.getLength(); i++) {
	    Node n = nl.item(i);
	    if (n.getNodeType() == Node.TEXT_NODE) {
		text += n.getNodeValue();
	    }
	}
	return text;
    }

}
