package net.sourceforge.czt.zml2html.testing.clients.cmdlineclient;

import net.sourceforge.czt.zml2html.testing.*;

import java.util.Iterator;
import java.io.File;

/**
 * Representation of an HTML frame.
 */
public class CmdlineClient 
{

    /* recognized parameter names */
    public static final String[] acceptableParameters =
    {"help", "hierarchy", "regression"};

    public static final int HIERARCHY = 0;
    public static final int REGRESSION = 1;

    private int command = -1;
    private boolean showHelp;

    public CmdlineClient(String[] args)
    {
	processParameterList(args);
	if (!checkParameters())
	    System.exit(-1);
	process();
    }

    public static void main(String[] args)
    {
	System.out.println(CmdlineClient.getPropaganda());
	new CmdlineClient(args);
    }

    public void process()
    {
	String path = "testcases";
	File dir = new File(path);
	Testset rootTestset = new Testset(true, null, dir);
	rootTestset.populate(true);

	if (command == HIERARCHY) {
	    printIndentedTestsets(rootTestset, 0);
	}
    }

    private void printIndentedTestsets(Testset parent, int indent)
    {
	printIndent(parent.getName(), indent);
	Iterator i = parent.getTestsets();
	while (i.hasNext()) {
	    Testset testset = (Testset)i.next();
	    printIndentedTestsets(testset, indent+1);
	}
    }

    private void printIndent(String s, int indentLength)
    {
	StringBuffer indent = new StringBuffer();
	for (int i = 0; i < indentLength; i++)
	    indent.append("\t");
	System.out.println(indent+s);
    }

    /**
     * Checks whether the supplied parameters make sense (semantically).
     */
    private boolean checkParameters()
    {
	switch (this.command) {
	case -1:
	    System.out.println(getHelpText());
	    System.exit(-1);
	case HIERARCHY:
	    return true;
	case REGRESSION:
	    return true;
	}
	return false;
    }

    /**
     * Gives the text intended for command line help.
     */
    public String getHelpText()
    {
	StringBuffer sb = new StringBuffer();
	sb.append("\nUsage:\n\tjava net.sourceforge.czt.zml2html.testing.clients.cmdlineclient.CmdlineClient [OPTIONS]\n");
	sb.append("Options:\n");
	sb.append("  -hierarchy\tShow testcase hierarchy\n");
	sb.append("  -regression\tShow testcase hierarchy\n");

	return sb.toString();
    }

    /**
     * Gives two-line project id line with project name, author info etc.
     */
    public static String getPropaganda()
    {
	StringBuffer sb = new StringBuffer();
	sb.append("ZML2HTML Testing Framework CMD line utility\n");
	return sb.toString();
    }

    /**
     * Processes the given name/value pair according to semantics
     * specified in the method body.
     *
     * @param paramName name of the parameter
     * @param paramValue value of the parameter
     */
    private void processParameter(String paramName, String paramValue)
    {
	if (paramName.equals("help")) {
	    this.showHelp = true;
	} else if (paramName.equals("hierarchy")) {
	    this.command = HIERARCHY;
	} else if (paramName.equals("regression")) {
	    this.command = REGRESSION;
	}
    }

    /**
     * Ensures that all parameters are recognized and
     * causes them to be interpreted.
     *
     * @param args The parameters.
     */
    private void processParameterList(String[] args)
    {
	String paramName = null;
	String paramValue = "";
	for (int i = 0; i < args.length; i++) {
	    int cutPoint = args[i].indexOf("=");
	    if (cutPoint < 0)
		cutPoint = args[i].length();
	    paramName = args[i].substring(1, cutPoint);      
	    if (!isRecognizedParameterType(paramName))
		throw new RuntimeException("'"+paramName+"'is not a recognized parameter name");

	    if (cutPoint >= 0 && cutPoint < args[i].length())
		paramValue = args[i].substring(cutPoint+1);

	    //          System.out.println(paramName);
	    //          System.out.println(paramValue);

	    processParameter(paramName, paramValue);
	}
    }

    /**
     * Determines whether a given parameter is recognized
     * (by name).
     *
     * <p/>This method does not check the validity of the given
     * parameter's payload.
     */
    private boolean isRecognizedParameterType(String param)
    {
	for (int i = 0; i < acceptableParameters.length; i++) {
	    if (param.startsWith(acceptableParameters[i]))
		return true;
	}
	return false;
    }

}
