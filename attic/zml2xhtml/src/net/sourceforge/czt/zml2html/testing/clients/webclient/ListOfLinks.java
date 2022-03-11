package net.sourceforge.czt.zml2html.testing.clients.webclient;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class ListOfLinks extends ArrayList
{
    /** List of the names of frames that will be updated by links contained in this <code>ListOfLinks</code> */
    private List frameNames;

    /** Name of the javascript function name to load multiple frames from one link */
    private String javascriptFunctionName;

    public ListOfLinks()
    {
	this(new ArrayList());
    }

    public ListOfLinks(List frameNames)
    {
	this.javascriptFunctionName = "load"+UniqueID.get();
	this.frameNames = frameNames;
    }

    public String getJavascriptFunctionName()
    {
	return this.javascriptFunctionName;
    }

    public String getJavascriptFrameloadingFunction()
    {
	String functionName = "load";
	StringBuffer fun = new StringBuffer();

	fun.append("<SCRIPT language='JavaScript'>\n");
	fun.append("function "+javascriptFunctionName+"(");
	
	// parameter signature
	for (int i = 1; i <= frameNames.size(); i++) {
	    String paramName = "url"+i;
	    fun.append(paramName);
	    if (i < frameNames.size())
		fun.append(",");
	}

	fun.append(") {\n");

	int assignmentCount = 0;
	Iterator frameNamesIter = frameNames.iterator();
	while (frameNamesIter.hasNext()) {
	    String frameName = (String)frameNamesIter.next();
	    fun.append("parent.");
	    fun.append(frameName);
	    fun.append(".location.href=url");
	    fun.append(++assignmentCount);
	    fun.append(";\n");
	}
		
	fun.append("}\n");	
	fun.append("</SCRIPT>\n");

	return fun.toString();
    }

    public void addLink(Link link)
    {
	link.setOwningList(this);
	add(link);
    }

    private static class UniqueID {	
	static long current= System.currentTimeMillis();
	
	static public synchronized String get() {
	    int uniqueInt = (new Long(current++)).intValue();
	    String s = "a"+uniqueInt;
	    return (s.hashCode()+"").substring(1);
	}
    }

}
