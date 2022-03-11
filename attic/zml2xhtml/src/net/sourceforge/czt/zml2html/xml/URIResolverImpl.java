package net.sourceforge.czt.zml2html.xml;

import javax.xml.transform.URIResolver;
import javax.xml.transform.Source;
import javax.xml.transform.stream.StreamSource;
import javax.xml.transform.TransformerException;

import java.io.File;

/**
 * Resolves URIs to be accessible by JAXP Transformers.
 *
 */
public class URIResolverImpl implements URIResolver
{
    private net.sourceforge.czt.zml2html.xml.Transformer transformer;

    public URIResolverImpl(net.sourceforge.czt.zml2html.xml.Transformer transformer)
    {
	this.transformer = transformer;
    }

    public Source resolve(String href, String base)
	throws TransformerException
    {
	StreamSource returnStreamSource = null;
	try {
	    //System.out.println(transformer.getBase()+href);	

	    returnStreamSource = new StreamSource(new File(transformer.getBase()+href));
	    return returnStreamSource;
	} catch(net.sourceforge.czt.zml2html.xml.TransformerException te) {
	    throw new TransformerException(te);
	}
    }
}
