package net.sourceforge.czt.zml2html.xml;

import org.w3c.dom.Document;

import java.io.IOException;
import java.io.Writer;

/**
 * Base implementation for all classes that write XML.
 */
public abstract class AbstractXMLWriter implements XMLWriter
{

    /**
     * Returns the serialized version of parameter <code>document</code>.
     *
     * @param document The document to be serialized.
     *
     * @returns Serialized version of <code>document</code>.
     */
    public abstract String getSerialization(Document document)
	throws XMLException;
    
    /**
     * Writes the serialization of <code>document</code>
     * to <code>target</code>
     *
     * @param document document to be serialized
     * @param target output location specification
     *
     * @throws IOException if an I/O error occurred while attempting
     *   to write.
     */
    public void write(Document document, OutputTarget target)
	throws IOException, XMLException
    {
	Writer writer = null;
	try {
	    writer = target.getWriter();
	    String serialization = getSerialization(document);
	    writer.write(serialization);
	} finally {
	    if (writer != null)
		writer.close();
	}
    }
}
