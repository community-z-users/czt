package net.sourceforge.czt.zml2html.xml;

import org.w3c.dom.Document;

import java.io.IOException;

/**
 * Interface for classes that can write a DOM to a file
 */
public interface XMLWriter
{

    /**
     * Returns the serialized version of parameter <code>document</code>.
     *
     * @param document The document to be serialized.
     *
     * @returns Serialized version of <code>document</code>.
     */
    public String getSerialization(Document document)
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
	throws IOException, XMLException;

}
