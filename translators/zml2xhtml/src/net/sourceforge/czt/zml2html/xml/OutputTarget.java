package net.sourceforge.czt.zml2html.xml;

import java.io.Writer;
import java.io.IOException;

/**
 * Interface for defining where to store a SmartDocument.
 */
public interface OutputTarget
{
    /**
     * Get a java.io.Writer for this OutputTarget
     *
     * @throws IOException if the Writer could not be constructed
     */
    public Writer getWriter()
	throws IOException;
}
