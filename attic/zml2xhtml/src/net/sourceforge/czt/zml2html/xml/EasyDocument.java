package net.sourceforge.czt.zml2html.xml;

import java.io.File;
import java.io.IOException;

import org.w3c.dom.Document;

/**
 * Facade for <code>SmartDocument</code>.
 *
 * <p>Developers are encouraged to subclass <code>EasyDoc</code>
 * for XML filetypes that they are working with; see the
 * <code>ZMLDocument</code> example subclass.</p>
 *
 * <p>The ZML example: suppose you want to
 * parse, transform, and validate a ZML file
 * using this class.</p>
 *
 * <code>
 *    EasyDocument easyDoc = new EasyDocument("/research/zml/specification.zml");<br/>
 *    <br/>
 *    // ensure that we have a validating ZML parser pool<br/>
 *    PooledParserFactory ppFactory = PooledParserFactory.getSingleton();<br/>
 *    if (!ppFactory.hasPool("zml_validating"))<br/>
 *      ppFactory.addPool(getZMLValidatingFactory(), "zml_validating");<br/>
 *<br/>
 *    if (easyDoc.isValid("zml_validating"))<br/>
 *      System.out.println("The document "+easyDoc+" is valid");<br/>
 *<br/>
 *    InputSource inputSource = new FileInputSource("/research/zml/Z.xsl");<br/>
 *    Transformer transformer = new XSLTTransformer(inputSource);<br/>
 *    SmartDocument newDoc = easyDoc.transform(transformer);<br/>
 *    newDoc.write("/research/zml/changed_transformation.zml");<br/>
 * </code>
 *
 *
 *
 */
public class EasyDocument extends SmartDocument
{
    private ActionReport validationActionReport;

    public EasyDocument(String path)
	throws XMLException, IOException
    {
	this(new File(path));		
    }

    /**
     * Creates a new <code>EasyDocument</code> instance.
     *
     * @param file a <code>File</code> value
     * @exception XMLException if an error occurs
     */
    public EasyDocument(File file)
      throws XMLException, IOException
    {
	super(new FileInputSource(file));
    }    

    public EasyDocument(File file, String parserPoolId)
	throws XMLException, IOException
    {
	super(new FileInputSource(file), parserPoolId);
    }    

    public EasyDocument(Document dom) {
	super(dom);
    }

    public SmartDocument transform(String path)
	throws TransformerException
    {
	return transform(new File(path));
    }

    public SmartDocument transform(File file)
	throws TransformerException
    {
	try {
	    FileInputSource inputSource = new FileInputSource(file);
	    XSLTTransformer transformer = new XSLTTransformer(inputSource);
	    return transform(transformer);
	} catch (XMLException xmle) {
	    throw new TransformerException(xmle);
	} catch (IOException ioe) {
	    throw new TransformerException(ioe);
	}
    }

    /**
     * 'Valid' here means "valid according to a W3C Schema"
     */
    public boolean isValid(String validatorId)
	throws ValidationException
    {
	//	System.out.println("checking validity using validating parser '"+validatorId+"'.");
	Validator validator = new W3CSchemaValidator(validatorId);
	try {
	    return isValid(validator);
	} finally {
	    this.validationActionReport = validator.getActionReport();
	}
    }

    public ActionReport getValidationActionReport()
    {
	return this.validationActionReport;
    }

    public void write(String path)
	throws XMLException
    {
	write(new File(path));
    }

    public void write(File file)
	throws XMLException
    {
	try {
	    write(new FileOutputTarget(file));
	} catch (IOException ioe) {
	    throw new XMLException(ioe);
	}
    }

}
