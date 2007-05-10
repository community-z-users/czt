package net.sourceforge.czt.zml2html.xml;

import java.io.File;
import java.io.IOException;
import java.io.FileReader;
import java.io.BufferedReader;
import java.io.Reader;

/**
 * An InputSource based on a file.
 */
public class FileInputSource implements InputSource
{
    private File inputFile;

    /**
     * Create a new FileInputSource based on <code>inputFile</code>
     *
     */
    FileInputSource(File inputFile) 
    {
	this.inputFile = inputFile;	
    }

    /**
     * Returns the Reader required by the InputSource interface
     */
    public Reader getInputReader()
	throws IOException
    {
	return new BufferedReader(new FileReader(inputFile));
    }

    public String getBase()
	throws ResourceUnavailableException
    {
	return inputFile.getParent()+"/";
    }
    
    public File getFile()
	throws ResourceUnavailableException
    {
	return inputFile;
    }

}

