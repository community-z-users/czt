package net.sourceforge.czt.zml2html.xml;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;

import java.util.Map;
import java.util.HashMap;

import java.io.File;
import java.io.IOException;

import org.apache.xpath.*;

/**
 * 
 * <p>A SmartDocument wraps a W3C DOM document
 * and provides pluggable validation, transformation
 * and comparison services.</p>
 *
 * <p>For convenient access to this functionality,
 * <code>SmartDocument</code>'s subclass
 * EasyDocument provides
 * a convenience facade.</p>
 *
 * <code>
 *    InputSource inputSource = new FileInputSource(new File("/research/zml/specification.zml"));<br/>
 *    SmartDocument smartDoc = new SmartDoc(inputSource);<br/>
 *    <br/>
 *    // ensure that we have a validating ZML parser pool<br/>
 *    PooledParserFactory ppFactory = PooledParserFactory.getSingleton();<br/>
 *    if (!ppFactory.hasPool("zml_validating"))<br/>
 *      ppFactory.addPool(getZMLValidatingFactory(), "zml_validating");<br/>
 *<br/>
 *    Validator validator = new W3CSchemaValidator(validatorId);<br/>
 *    if (smartDoc.isValid(validator))<br/>
 *      System.out.println("The document "+smartDoc+" is valid");<br/>
 *<br/>
 *    InputSource inputSource = new FileInputSource("/research/zml/Z.xsl");<br/>
 *    Transformer transformer = new XSLTTransformer(inputSource);<br/>
 *    SmartDocument newDoc = smartDoc.transform(transformer);<br/>
 *<br/>
 *    OutputTarget outputTarget = new FileOutputTarget(new File("/research/zml/changed_transformation.zml"));<br/>
 *    newDoc.write(outputTarget);<br/>
 * </code>
 *
 */
public class SmartDocument
{
    /* Access to the XML source */
    protected InputSource inputSource = null;

    /* ActionListener for the action of parsing this SmartDocument */
    private ParseActionListener parseActionListener = null;

    /* DOM representation of the document instance */
    private Document dom = null;

    /* String indicating which parser pool this SmartDocument uses */
    private String parserPoolId;

    /* The transformers associated with this SmartDocument */
    private Map transformers = new HashMap();

    /* Default Transformer Id */
    private String defaultTransformerId = "default";

    /* Default XMLWriter Id */
    private String defaultXMLWriterId = "default";
    
    /**
     * Some testing code
     */
    public static void main(String[] args)
    {
	String filename = "/research/development/zml/testcases/x.zml";
	if (args.length > 0)
	    filename = args[0];

	InputSource is = null;
	InputSource xslIs = null;
	try {
	    is = new FileInputSource(new File(filename));
	    xslIs = new FileInputSource(new File("/research/development/zml/play/Z.xsl"));
	} catch (RuntimeException ioe) {	    
	    ioe.printStackTrace();
	    return;
	}
	SmartDocument sd = null;
	XSLTTransformer xsldoc = null;

	System.out.print("creating SmartDocument... ");
	try {
	    sd = new SmartDocument(is);
	    xsldoc = new XSLTTransformer(xslIs);
	} catch(XMLException xmle) {
	    xmle.printStackTrace();
	} catch(IOException ioe) {
	    ioe.printStackTrace();
	}

	sd.addTransformer("default", xsldoc, true);

	try {
	    sd.transformSelf();
	} catch(TransformerException te) {
	    te.printStackTrace();
	}

	try {
	    sd.write(new FileOutputTarget(new File("/research/development/HAHAHA.xml")));
	} catch (XMLException xmle) {
	    xmle.printStackTrace();
	} catch (IOException ioe) {
	    ioe.printStackTrace();
	}

	if (sd.isEqual(sd))
	    System.out.println("sd.equals(sd)!");
	else
	    System.out.println("!sd.equals(sd) -- something is messed up");

	boolean valid = false;
	try {
	    valid = sd.isValid(new W3CSchemaValidator("default"));
	} catch (ValidationException ve) {
	    ve.printStackTrace();
	}

	if (valid)
	    System.out.println("This is a valid ZML document");
	else {
	    System.out.println("This is not a valid ZML document");
	}
	
	
	System.out.println("done.");
    }

    public SmartDocument() {}

    /**
     * Creates a new SmartDocument based on the given source.
     *
     * @param inputSource Description of the input document location
     *
     * @throws XMLException if the given document cannot be parsed
     *
     */
    public SmartDocument(InputSource inputSource)
	throws XMLException, IOException
    {
	this(inputSource, "default");
    }

    /*
     * Creates a new SmartDocument based on the given source,
     * parsed with the indicated Parser.
     *
     * Note that obtaining parses through the <code>getParser()</code>
     * facility is preferred over setting a custom factory because
     * it facilitates caching of parsers.
     *
     * @param inputSource Description of the input document location
     * @param parserPoolId id of the parser pool to be used
     *
     * @throws XMLException if the input source could not be accessed
     *  - if the required parser could not be invoked
     *  - if the input document is not well formed
     *
     */
    public SmartDocument(InputSource inputSource, String parserPoolId)
	throws XMLException, IOException
    {
	this.inputSource = inputSource;
	this.parserPoolId = parserPoolId;
	this.parseActionListener = new ParseActionListener(this);
	this.parseSelf();
    }

    /**
     * Creates a new SmartDocument from the passed Node <code>node</code>.
     *
     * @param node The node from which to generate the SmartDocument.
     *
     */
    public SmartDocument(Document dom) {
	// need to create ParseActionListener?
	// need to set parserPoolId?
	// no InputSource for this SmartDocument

	this.dom = dom;
    }

    /**
     * Writes the DOM representation of the <code>SmartDocument</code>
     * to the location specified by <code>target</code>.
     *
     * @param target location specification
     *
     * @throws XMLException
     * 
     */
    public void write(OutputTarget target)
	throws XMLException
    {
	XMLWriter xmlWriter = getXMLWriter();
	try {
	    xmlWriter.write(this.dom, target);
	} catch (IOException ioe) {
	    throw new XMLException(ioe);
	}
    }

    public String getXMLAsString()
	throws XMLException
    {
	XMLWriter xmlWriter = getXMLWriter();
	return xmlWriter.getSerialization(this.dom);
    }

    /**
     * Writes the <code>SmartDocument</code> to the file it was originally
     * read from.
     *
     * @throws ResourceUnavailableException if the <code>SmartDocument</code>
     *   was not initially read from a File, but from another type of input
     *   (e.g. a stream) that can not be written back to.
     */
    public void write()
	throws ResourceUnavailableException, XMLException, IOException
    {
	File file = this.inputSource.getFile();
	FileOutputTarget target = new FileOutputTarget(file);
	write(target);
    }

    /**
     * Returns an XMLWriter based on this instance's preferences.
     *
     * <b>Note:</b> This method always returns a new XMLWriter instance
     *  when it is called. This needs to be changed to a
     *  caching/pooled solution as soon as there's time.
     *
     */
    public XMLWriter getXMLWriter()
      throws XMLException
    {
	try {
	    return new IndentingXMLWriter();
	} catch (TransformerException te) {
	    throw new XMLException(te);
	}
    }

    /**
     * Adds a transformer to this SmartDocument for later use.
     * 
     * @param id The id by which this transformer will be referenced
     * @param transformer the Transformer instance to be registered
     * @param isDefault indicate whether this is the default transformer
     *    for the SmartDocument.
     */
    public void addTransformer(String id, Transformer transformer, boolean isDefault)
    {
	transformers.put(id, transformer);

	if (isDefault) {
	    this.defaultTransformerId = id;
	}
    }

    /**
     * Adds a Transformer instance to this SmartDocument for later use.
     *
     * The added transformer will become the default transformer
     */
    public void addTransformer(String id, Transformer transformer)
    {
	addTransformer(id, transformer, true);
    }

    /**
     * Returns the default Rransformer for this SmartDocument.
     *
     * @return The Default Transformer
     *
     * @throws TransformerException if there is no default transformer, or the indicated
     *   default transformer cannot be located.
     */
    public Transformer getDefaultTransformer()
	throws TransformerException
    {
	if (this.defaultTransformerId == null || this.defaultTransformerId.equals(""))
	    throw new TransformerException("No default transformer has been indicated");
	Transformer defaultTransformer = (Transformer)transformers.get(this.defaultTransformerId);
	if (defaultTransformer == null)
	    throw new TransformerException("The indicated default transformer cannot be located");
	return defaultTransformer;
    }

    /**
     * Performs a transformation using the default Transformer.
     *
     * @throws XMLException if the transformation failed
     *
     * @return the SmartDocument representation of the
     * transformation result
     */
    public SmartDocument transform()
	throws TransformerException
    {
	return transform(getDefaultTransformer());
    }

    /**
     * Performs a transformation using the named Transformer.
     
     * @param transformerId identifies the transformer to use
     *
     * @throws XMLException
     *   - if there was a transformation error
     *
     */
    public SmartDocument transform(String transformerId)
	throws TransformerException
    {
	return transform(getTransformer(transformerId));
    }

    /**
     * Transform the Document with the passed Transformer.
     */
    public SmartDocument transform(Transformer transformer)
	throws TransformerException
    {
	return new SmartDocument(transformer.transform(this.dom));
    }


    /**
     * Performs a transformation using the supplied Transformer
     * and changes the instance DOM to the Transformation's
     * output DOM.
     *
     */
    public void transformSelf(Transformer transformer)
	throws TransformerException
    {
	this.dom = transformer.transform(this.dom);
    }

    public void transformSelf(String transformerId)
	throws TransformerException
    {
	transformSelf(getTransformer(transformerId));
    }

    public void transformSelf()
	throws TransformerException
    {
	transformSelf(getDefaultTransformer());
    }

    public Transformer getTransformer(String transformerId)
	throws TransformerException
    {
	Transformer t = (Transformer)transformers.get(transformerId);

	if (t == null) {
	    throw new TransformerException("Cannot use transformer identified by '"+transformerId+"'; no "+
					   "such Transformer has been registered");
	}

	return t;	
    }


    /**
     * Adds a Validator to this SmartDocument for later use.
     * 
     * @param id The id by which this Validator will be referenced
     * @param transformer the Validator instance to be registered
     * @param isDefault indicate whether this is the default validator
     *    for this instance.
     */
    public void addValidator(String id, Validator validator)
    {
    }

    /**
     * Determine whether the current document is valid with respect
     * to the default validator.
     *
     * @return <code>true</code> if the default Validator validates
     * this document, else <code>false</code>
     *
     * throws XMLException
     *  - if there is no default validator
     *  - if an error occurred during validation
     */
    public boolean isValid(Validator validator)
	throws ValidationException
    {
	return validator.isValid(this, true);
    }

    /**
     * Determine whether the current document is valid with respect
     * to the given Validator.
     *
     * @return <code>true</code> if the default Validator validates
     * this document, else <code>false</code>
     *
     * throws XMLException
     *  - if there is no default validator
     *  - if an error occurred during validation
     */
    
    /**
     * Adds a Comparator to this SmartDocument for later use.
     *
     * @param id Theid by which this Comparator will be referenced
     * @param comparator The Comparator to be added
     */
    public void addComparator(String id, Comparator comparator)
    {
    }

    /**
     * Compares the SmartDocument with the passed SmartDocument
     * <code>doc</code> based on the default comparator.
     * Implementation of the java.lang.Comparable interface.
     *
     * @param doc The SmartDocument to compare to
     *
     * @return true if the default Comparator determines
     *  both SmartDocuments are equal
     *
     * @throws XMLException
     *   - if there is no default Comparator
     *   - if an error occurred during comparison
     *
     */


    /**
     * Compares the SmartDocument with the passed SmartDocument
     * <code>doc</code> based on the passed Comparator.
     *
     * @param doc The SmartDocument to compare to
     * @param comparator The Comparator that performs the comparison
     *
     * @return true if the default Comparator determines
     *  both SmartDocuments are equal
     *
     * @throws XMLException
     *   - if there is no default Comparator
     *   - if an error occurred during comparison
     *
     */
    /**
     * <b>Note:</b> Needs to be integrated.
     */ 
    public boolean isEqual(SmartDocument sd)
    {
	Comparator comparator = new EqualityComparator();
	return comparator.isEqual(this.dom, sd.getDOM());
    }

    /**
     * Parses this SmartDocument and stores its DOM representation.
     *
     * XXX: need to use actionlistener here
     */
    private void parseSelf()
	throws XMLException, IOException
    {
	Document doc = null;  // the resulting document
	DocumentBuilder parser = getParser();
	org.xml.sax.InputSource is = null;
	try {
	    is = new org.xml.sax.InputSource(this.inputSource.getInputReader());
	    doc = parser.parse(is);
	} catch (IOException e) {
	    throw e;
	} catch (Exception e) {
	    throw new XMLException(e);
	}

	PooledParserFactory ppFactory = PooledParserFactory.getSingleton();
	ppFactory.release(parser);

	this.dom = doc;
    }

    /**
     * Obtains a parser for the SmartDocument and performs a parse
     * on the InputSource, writing error handling information
     * to this instance's ParseActionListener.
     */
    private Document parse(String actionDescription, org.xml.sax.InputSource inputSource)
    {
	Document doc = null; // the document to be returned
	DocumentBuilder parser = null;
	try {
	    parser = getParser();
	    this.parseActionListener.startAction(actionDescription);
	    parser.setErrorHandler(this.parseActionListener);
	    doc = parser.parse(inputSource);
	} catch (Exception e) {
	    e.printStackTrace();
	    //	    throw e;
	} finally {
	    parser.setErrorHandler(null);
	    try {
		this.parseActionListener.endAction();
	    } catch (IllegalStateException ise) {
		// ignore thispexception because we already know the
		// parse resulted in an exception
	    }
	}
	
	return doc;
    }

    /**
     * Obtain the DOM wrapped by the <code>SmartDocument</code>.
     */
    public Document getDOM()
    {
	return this.dom;
    }

    public InputSource getInputSource()
    {
	return this.inputSource;
    }

    /**
     * Obtains the appropriate parser for this SmartDocument from the
     * PooledParserFactory.
     * If a custom DocumentBuilderFactory has been registered for
     * this SmartDocument, it is added to the pool and 
     * one of its parsers returned.
     *
     * <b>Note</b>: A parser obtained from this method
     * <i>must</i> be closed using the PooledParserFactory.release(DocumentBuilder)
     * method.
     *
     * @return A Parser from the PooledParserFactory.
     *
     */
    private DocumentBuilder getParser()
    {	
	PooledParserFactory ppFactory = PooledParserFactory.getSingleton();
	DocumentBuilder parser = null;
	
	parser = ppFactory.getParser(this.parserPoolId);

	if (parser == null)
	    throw new RuntimeException("Oops. Parser reference is null, which should never happen");
	    
	return parser;
    }

    /**
     * Releases a cached Parser back into its pool.
     *
     * @param parser the Parser to release.
     */
    public static void releaseParser(DocumentBuilder parser)
    {
	PooledParserFactory ppFactory = PooledParserFactory.getSingleton();
	ppFactory.release(parser);
    }


}












