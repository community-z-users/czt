package net.sourceforge.czt.zml2html.xml;

import java.io.Reader;
import java.io.File;
import java.io.IOException;

/**
 * Abstraction for retreiving XML input
 *
 */
public interface InputSource
{
    public Reader getInputReader()
	throws IOException;

    public String getBase()
	throws ResourceUnavailableException;
    
    public File getFile()
	throws ResourceUnavailableException;

}



