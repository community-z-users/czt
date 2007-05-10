package net.sourceforge.czt.zml2html.xml;

import java.io.Writer;
import java.io.IOException;

/**
 * An OutputTarget that saves XML output to a java.io.Writer.
 */
public class WriterOutputTarget implements OutputTarget
{
    private Writer outputWriter = null;

    /**
     * Create a new WriterOutputTarget based on <code>outputWriter</code>.
     *
     * @param write the java.io.Writer to write XML output to
     */
    public WriterOutputTarget(Writer outputWriter)
    {
	this.outputWriter = outputWriter;
    }

    public WriterOutputTarget()
    {
    }

    /**
     * Retrieve the writer to output to.
     */
    public Writer getWriter()
	throws IOException
    {
	return this.outputWriter;
    }

    /**
     * Set the writer used for output. This method should
     * be used by subclasses of <code>WriterOutputTarget</code>.
     */
    protected void setOutputWriter(Writer outputWriter)
    {
	this.outputWriter = outputWriter;
    }

}




