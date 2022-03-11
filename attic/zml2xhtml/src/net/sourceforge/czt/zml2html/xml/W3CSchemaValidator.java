package net.sourceforge.czt.zml2html.xml;

import java.io.File;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.DocumentBuilder;

/**
 * Validates using W3C schema instances
 * that are available from a local filesystem.
 */
public class W3CSchemaValidator implements Validator
{
    private String validatingParserPoolId;
    private PooledParserFactory ppFactory;
    private ParseActionListener parseActionListener;

    public W3CSchemaValidator(String validatingParserPoolId)
	throws ValidationException
    {
	this.validatingParserPoolId = validatingParserPoolId;
	ppFactory = PooledParserFactory.getSingleton();		

	// xxx: ParseActionListener constructor expects a SmartDocument, but passing NULL is ok.
	//      Why isnt this a zero-arg constructor?...
	parseActionListener = new ParseActionListener(null);
    }

    public boolean isValid(SmartDocument inputDocument)
	throws ValidationException
    {
	return isValid(inputDocument, true);
    }

    public boolean isValid(SmartDocument inputDocument, boolean forceValidation)
	throws ValidationException
    {
	DocumentBuilder parser;
	try {
	    parser = ppFactory.getParser(this.validatingParserPoolId);
	    parser.setErrorHandler(this.parseActionListener);
	    parseActionListener.startAction("validating using w3c");
	    parser.parse(new org.xml.sax.InputSource(inputDocument.getInputSource().getInputReader()));
	} catch (Exception e) {
	    e.printStackTrace();
	    throw new ValidationException(e);
	} finally {
	    this.parseActionListener.endAction();
	}

	if (parseActionListener.getErrorCount() == 0)
	    return true;
	
	return false;
    }

    public ActionReport getActionReport()
    {
	return parseActionListener.getActionReport();
    }
}




