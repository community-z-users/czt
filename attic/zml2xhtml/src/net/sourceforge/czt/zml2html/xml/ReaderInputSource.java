package net.sourceforge.czt.zml2html.xml;

import java.io.Reader;
import java.io.IOException;

/**
 * Performs infrastructure required by all InputSources.
 */
public class ReaderInputSource extends AbstractInputSource
{
    /* The Reader retreiving XML input */
    private Reader inputReader = null;

    /**
     * Creates a new ReaderInputSource based on the passed
     * <code>inputReader</code>.
     *
     * @param inputReader A Reader that knows about the input
     *
     */
    public ReaderInputSource(Reader inputReader)
    {
	setInputReader(inputReader);
    }
    
    /**
     * Returns the Reader required by the InputSource interface
     */
    public Reader getInputReader()
	throws IOException
    {
	return this.inputReader;
    }
    
    /**
     * Used by subclasses to set the <code>inputReader</code>
     */
    protected void setInputReader(Reader inputReader)
    {
	this.inputReader = inputReader;
    }


}






