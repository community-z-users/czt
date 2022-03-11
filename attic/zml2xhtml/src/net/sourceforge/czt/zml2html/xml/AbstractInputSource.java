package net.sourceforge.czt.zml2html.xml;

import javax.xml.transform.TransformerException;

import java.io.File;

public abstract class AbstractInputSource implements InputSource
{
    public String getBase()
	throws ResourceUnavailableException
    {
	throw new ResourceUnavailableException("InputSource has no context information");
    }

    public File getFile()
	throws ResourceUnavailableException
    {
	throw new ResourceUnavailableException("InputSource has no context information");
    }

}
