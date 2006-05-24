package net.sourceforge.czt.eclipse.editors.latex;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.util.CZTColorManager;
import net.sourceforge.czt.eclipse.util.IZColorConstants;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

/**
 * @author Chengdong Xu
 */
public class ZLatexCodeScanner extends RuleBasedScanner {

	private static String[] fgAlphabeticKeywords = { "else", "false",
			"function", "generic", "if", "leftassoc", "let", "IP", "parents",
			"pre", "relation", "rightassoc", "section", "then", "true" };

	private static String[] fgSymbolicKeywords = { ":", "==", ",", "::=", "|",
			"&", "\\", "/", ".", ";", "-", ",,", "=", "" };

	/**
	 * A.2.4 Core characters and words in Latex markup
	 */
	// Greak alphabet characters
	private static String[] fgGreakCharacters = { "\\Delta", "\\Xi", "\\theta",
			"\\lambda", "\\mu" };

	// Other letter characters
	private static String[] fgOtherLetterCharacters = { "\\arithmos", "\\nat",
			"\\power" };

	// Special characters
	private static String[] fgSpecialCharacters = { "\\_", "\\{", "\\\\ldata}",
			"\\rdata", "\\lblot", "\\rblot" };

	// Symbol characters
	private static String[] fgSymbolCharacters = { "\\vdash", "\\land",
			"\\lor", "\\implies", "\\iff", "\\lnot", "\\forall", "\\exists",
			"\\cross", "\\in", "\\hide", "\\project", "\\semi", "\\pipe" };

	/**
	 * Creates a Z Latex code scanner
	 */
	public ZLatexCodeScanner(CZTColorManager colorManager) {
		IToken keywordToken = new Token(new TextAttribute(colorManager
				.getColor(IZColorConstants.KEYWORD)));
		IToken singleLineCommentToken = new Token(new TextAttribute(
				colorManager.getColor(IZColorConstants.SINGLE_LINE_COMMENT)));
		IToken otherToken = new Token(new TextAttribute(colorManager
				.getColor(IZColorConstants.DEFAULT)));

		List rules = new ArrayList();

		// Add rule for single line comments.
		rules.add(new EndOfLineRule("%", singleLineCommentToken, '%')); //$NON-NLS-1$
		// Add rule for strings and character constants.
		// rules.add(new SingleLineRule("\"", "\"", stringToken, '\\'));
		// //$NON-NLS-2$ //$NON-NLS-1$
		// rules.add(new SingleLineRule("'", "'", stringToken, '\\'));
		// //$NON-NLS-2$ //$NON-NLS-1$

		// Add generic whitespace rule.
		rules.add(new WhitespaceRule(new ZLatexWhitespaceDetector()));

		// Add word rule for keywords, types, tags and constants.
		WordRule wordRule = new WordRule(new ZLatexWordDetector(), otherToken);

		for (int i = 0; i < fgAlphabeticKeywords.length; i++)
			wordRule.addWord(fgAlphabeticKeywords[i], keywordToken);
		for (int i = 0; i < fgSymbolicKeywords.length; i++)
			wordRule.addWord(fgSymbolicKeywords[i], keywordToken);
		for (int i = 0; i < fgGreakCharacters.length; i++)
			wordRule.addWord(fgGreakCharacters[i], keywordToken);
		for (int i = 0; i < fgOtherLetterCharacters.length; i++)
			wordRule.addWord(fgOtherLetterCharacters[i], keywordToken);
		for (int i = 0; i < fgSpecialCharacters.length; i++)
			wordRule.addWord(fgSpecialCharacters[i], keywordToken);
		for (int i = 0; i < fgSymbolCharacters.length; i++)
			wordRule.addWord(fgSymbolCharacters[i], keywordToken);

		rules.add(wordRule);

		IRule[] result = new IRule[rules.size()];
		rules.toArray(result);
		setRules(result);
	}
}