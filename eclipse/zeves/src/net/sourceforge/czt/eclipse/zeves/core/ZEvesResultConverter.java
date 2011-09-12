package net.sourceforge.czt.eclipse.zeves.core;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.parser.zeves.ParseUtils;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.zeves.PrintUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;


public class ZEvesResultConverter {

	public static Pred parseZEvesPred(SectionManager sectInfo, String sectName, String zEvesPredStr)
			throws IOException, CommandException {

		Source source = createParseSource(zEvesPredStr);

		try {
			return ParseUtils.parsePred(source, sectName, sectInfo);
		} catch (CommandException e) {
			throw handleCommandException(e);
		}
	}
	
	public static Expr parseZEvesExpr(SectionManager sectInfo, String sectName, String zEvesExprStr)
			throws IOException, CommandException {
		
		Source source = createParseSource(zEvesExprStr);

		try {
			return ParseUtils.parseExpr(source, sectName, sectInfo);
		} catch (CommandException e) {
			throw handleCommandException(e);
		}
	}
	
	/**
	 * Parses given Z/Eves result string first as Expr and if that fails, tries
	 * parsing it as Pred
	 * 
	 * @param sectInfo
	 * @param sectName
	 * @param zEvesStr
	 * @return
	 * @throws IOException
	 * @throws CommandException
	 */
	public static Term parseZEvesResult(SectionManager sectInfo, String sectName, String zEvesStr)
			throws IOException, CommandException {
		
		try {
			return parseZEvesExpr(sectInfo, sectName, zEvesStr);			
		} catch (CommandException e) {
			return parseZEvesPred(sectInfo, sectName, zEvesStr);
		}
	}
	
	private static CommandException handleCommandException(CommandException e) {
		Throwable cause = e.getCause();
		
		if (cause instanceof ParseException) {
			ParseException pe = (ParseException) cause;
			cause = new ParseException(new ArrayList<CztError>(pe.getErrorList()));
			cause.setStackTrace(pe.getStackTrace());
			
			// clear previous errors - they are accumulating somehow
			pe.getErrorList().clear();
			
			CommandException ce = new CommandException(e.getMessage(), cause);
			ce.setStackTrace(e.getStackTrace());
			return ce;
		}
		
		return e;
	}

	private static Source createParseSource(String zEvesResultStr) {
		Source source = new StringSource(zEvesResultStr, "zevesResult");
		source.setMarkup(Markup.UNICODE);
		source.setEncoding("UTF-8");
		return source;
	}
	
	public static String printResult(SectionManager sectInfo, String sectName, Term term, 
			Markup markup, int textWidth) {

		SectionManager sectMan = sectInfo.clone();

		sectMan.setProperty(PrintPropertiesKeys.PROP_TXT_WIDTH, String.valueOf(textWidth));
		sectMan.setProperty(PrintPropertiesKeys.PROP_PRINT_ZEVES, "true");
		
		// just need this property set, but it isn't working :-(... see ZEves parser LatexScannerDebugger.java debugPrinter
		sectMan.setProperty(PrintPropertiesKeys.PROP_PRINTING_STRUCTURED_GOAL, "true");

		StringWriter out = new StringWriter();

		PrintUtils.print(term, out, sectMan, sectName, markup);

		return out.toString();
	}
	
	public static String convertPred(SectionManager sectInfo, String sectName, String zEvesPredStr,
			Markup markup, int textWidth) throws IOException, CommandException {
		
		Pred pred = parseZEvesPred(sectInfo, sectName, zEvesPredStr);
		return printResult(sectInfo, sectName, pred, markup, textWidth);
	}
	
	public static String convertExpr(SectionManager sectInfo, String sectName, String zEvesExprStr,
			Markup markup, int textWidth) throws IOException, CommandException {
		
		Expr expr = parseZEvesExpr(sectInfo, sectName, zEvesExprStr);
		return printResult(sectInfo, sectName, expr, markup, textWidth);
	}
	
	public static String convert(SectionManager sectInfo, String sectName, String zEvesStr,
			Markup markup, int textWidth) throws IOException, CommandException {
		
		Term term = parseZEvesResult(sectInfo, sectName, zEvesStr);
		return printResult(sectInfo, sectName, term, markup, textWidth);
	}
	
}
