package net.sourceforge.czt.zml2html.xml;

import java.io.File;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;


/**
 * A WriterOutputTarget based on a java.io.File.
 */
public class FileOutputTarget extends WriterOutputTarget
{
    /* The File containins XML input */
    private File outputFile = null;

    /**
     * Creates a new FileOutputTarget based on <code>outputFile</code>.
     *
     * @param outputFile the file to write XML output to
     *
     */
    public FileOutputTarget(File outputFile)
	throws IOException
    {
	this.outputFile = outputFile;
    }

    /**
     * Creates a new FileOutputTarget based on the file
     * located at location <code>path</code>.
     */
    public FileOutputTarget(String path)
	throws IOException
    {
	this(new File(path));
    }

    public Writer getWriter()
	throws IOException
    {
	return new BufferedWriter(new FileWriter(this.outputFile));
    }

}



