package net.sourceforge.czt.zml2html.testing;

import net.sourceforge.czt.zml2html.xml.*;

import java.io.File;
import java.io.IOException;

/**
 * Abstraction of an Approved ZML document.
 *
 * In addition to a regular <code>ZMLDocument</code>, an 
 * <code>ApprovedZMLDocument</code> contains a reference
 * to the specific XHTML output on which the approval
 * was based.
 */
public class ApprovedZMLDocument extends ZMLDocument
{
    private XHTMLDocument approvedOutput;

    public ApprovedZMLDocument(File file)
	throws XMLException, IOException
    {
	super (file);
	approvedOutput = new XHTMLDocument(new File(file.getParent(), file.getName()+".html"));
    }
   
    public XHTMLDocument getApprovedOutput()
    {
	return approvedOutput;
    }
}
