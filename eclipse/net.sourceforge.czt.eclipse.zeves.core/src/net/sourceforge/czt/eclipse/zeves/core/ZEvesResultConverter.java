package net.sourceforge.czt.eclipse.zeves.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.eclipse.core.document.DocumentUtil;
import net.sourceforge.czt.eclipse.zeves.core.internal.ZEvesCorePlugin;
import net.sourceforge.czt.parser.zeves.ParseUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ParenAnn;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZSect;


public class ZEvesResultConverter {

	public static Pred parseZEvesPred(SectionManager sectInfo, String sectName, String zEvesPredStr)
			throws IOException, CommandException {

		assertSectionAvailable(sectInfo, sectName);
		Source source = createParseSource(zEvesPredStr);
		return clean(ParseUtils.parsePred(source, sectName, sectInfo));
	}
	
	public static Expr parseZEvesExpr(SectionManager sectInfo, String sectName, String zEvesExprStr)
			throws IOException, CommandException {
		
		assertSectionAvailable(sectInfo, sectName);
		Source source = createParseSource(zEvesExprStr);
		return clean(ParseUtils.parseExpr(source, sectName, sectInfo));
	}
	
	public static List<Para> parseZEvesParas(SectionManager sectInfo, String sectName, String zEvesExprStr)
			throws IOException, CommandException {
		
		assertSectionAvailable(sectInfo, sectName);
		Source source = createParseSource(zEvesExprStr);
		List<Para> paras = ParseUtils.parseParas(source, sectName, sectInfo);
		List<Para> cleanedParas = new ArrayList<Para>(paras.size());
		for (Para para : paras) {
			cleanedParas.add(clean(para));
		}
		
		return cleanedParas;
	}

	private static class DeleteParenAnnVisitor implements TermVisitor<Object> {

		@Override
		public Object visitTerm(Term term) {
			VisitorUtils.visitTerm(this, term);
			for (Iterator<?> annIt = term.getAnns().iterator(); annIt.hasNext(); ) {
				Object ann = annIt.next();
				if (ann instanceof ParenAnn) {
					annIt.remove();
				}
			}
			return null;
		}
	}
	
	private static final TermVisitor<?> DELETE_ANNS = new DeleteParenAnnVisitor();

	private static <T extends Term> T clean(T term) {
		// drop extra annotations (e.g. ParenAnn, etc), which will result in more canonical
		// representation of Z/EVES results in CZT
		term.accept(DELETE_ANNS);
		return term;
	}


	/**
	 * Parses given Z/EVES result string first as Expr and if that fails, tries
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
	
	/**
	 * Asserts that the converted section is actually available in the section
	 * manager. Otherwise, the parsing will fail anyway - so we produce a
	 * nicer/simpler exception to indicate that the section is not available.
	 * 
	 * @param sectInfo
	 * @param sectName
	 * @throws CommandException
	 */
	private static void assertSectionAvailable(SectionManager sectInfo, String sectName)
			throws CommandException {
		
		Key<ZSect> sectKey = new Key<ZSect>(sectName, ZSect.class);
		if (!sectInfo.isCached(sectKey)) {
			throw new CommandException(sectInfo.getDialect(), "Section " + sectName + " is not parsed.");
		}
	}
	
	private static Source createParseSource(String zEvesResultStr) {
		Source source = new StringSource(zEvesResultStr, "zevesResult");
		source.setMarkup(Markup.UNICODE);
		source.setEncoding("UTF-8");
		return source;
	}
	
	public static String printResult(SectionManager sectInfo, String sectName, Term term, 
			Markup markup, int textWidth, boolean display) {
		
		try {
			assertSectionAvailable(sectInfo, sectName);
			return DocumentUtil.print(term, sectInfo, sectName, markup, textWidth, display);
		} catch (CommandException e) {
			// problems printing
			ZEvesCorePlugin.getDefault().log(e);
			return null;
		}
	}
	
	public static String convertPred(SectionManager sectInfo, String sectName, String zEvesPredStr,
			Markup markup, int textWidth, boolean display) throws IOException, CommandException {
		
		Pred pred = parseZEvesPred(sectInfo, sectName, zEvesPredStr);
		return printResult(sectInfo, sectName, pred, markup, textWidth, display);
	}
	
	public static String convertExpr(SectionManager sectInfo, String sectName, String zEvesExprStr,
			Markup markup, int textWidth, boolean display) throws IOException, CommandException {
		
		Expr expr = parseZEvesExpr(sectInfo, sectName, zEvesExprStr);
		return printResult(sectInfo, sectName, expr, markup, textWidth, display);
	}
	
	public static String convert(SectionManager sectInfo, String sectName, String zEvesStr,
			Markup markup, int textWidth, boolean display) throws IOException, CommandException {
		
		Term term = parseZEvesResult(sectInfo, sectName, zEvesStr);
		return printResult(sectInfo, sectName, term, markup, textWidth, display);
	}
	
	public static String convertParas(SectionManager sectInfo, String sectName, String zEvesParasStr,
			Markup markup, int textWidth, boolean display) throws IOException, CommandException {
		
		List<Para> paras = parseZEvesParas(sectInfo, sectName, zEvesParasStr);
		
		StringBuilder out = new StringBuilder();
		
		String delim = "";
		for (Para para : paras) {
			out.append(delim).append(printResult(sectInfo, sectName, para, markup, textWidth, display));
			delim = "\n";
		}
		
		return out.toString();
	}
	
}
