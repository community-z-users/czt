package net.sourceforge.czt.zml2html.xml;

import org.w3c.dom.Document;

import java.util.List;
import java.io.File;

/**
 * Transformers generate SmartDocument instances based on
 * an input (source) document.
 *
 */
public interface Transformer
{
    /*
     * Returns a new SmartDocument instance based on
     * an inputDocument.
     *
     * Since no ActionReport instance is provided for
     * action reporting, the Transformer instance
     * must provide its own.
     *
     * @return a new SmartDocument representing the outcome
     * of the transformation process.
     *
     * @throws XMLException is throws when the transformation
     *   could not be performed. The underlying cause is contained
     *   in the XMLException.
     *
     */
    public Document transform(Document inputDocument)
	throws TransformerException;

    /**
     * Returns a new SmartDocument instance based on <code>inputDocument</code>,
     * writing status and error information from the Transformation action
     * to the supplied <code>actionReport</code> instance.
     *
     * @param inputDocument document to be transformed
     * @param actionReport ActionReport instance to use for error callbacks.
     */
    public Document transform(Document inputDocument, TransformActionListener transformActionListener)
	throws TransformerException;

    /*
     * Returns an ActivityReport describing the last transformation
     * performed by the current instance.
     *
     * This method is typically called after transform(SmartDocument)
     * has thrown an XMLException, and the error cause needs to be
     * analyzed.
     *
     * @return An ActionReport describing the results of the last
     * transform(SmartDocument) call.
     *
     * @throws IllegalStateException if this method is called 
     * on a Transformer that has never performed an operation.
     */
    public TransformActionReport getTransformActionReport();

    /**
     * A String identifying this transformer object.
     *
     * This should include the type of transformation used
     * (e.g. XSLT), the transformation engine and version
     * used, etc.
     */
    public String getTransformerInfo();

    public String getBase()
	throws TransformerException;

    public File getFile()
	throws TransformerException;

}


