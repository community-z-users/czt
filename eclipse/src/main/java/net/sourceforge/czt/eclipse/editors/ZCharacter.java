/**
 * 
 */
package net.sourceforge.czt.eclipse.editors;

/**
 * @author Chengdong Xu
 *
 */
public class ZCharacter {

	/**
	 * 
	 */
	public ZCharacter() {
		super();
		// TODO Auto-generated constructor stub
	}
	
	public static boolean isZWordStart(char character){
		return isZLatexWordStart(character) ||
				isZUnicodeWordStart(character);
	}
	
	public static boolean isZLatexWordStart(char character) {
		return Character.isLetter(character) || (character == '\\');
	}
	
	public static boolean isZUnicodeWordStart(char character) {
		return Character.isLetter(character);
	}
	
	public static boolean isZWordPart(char character) {
		return isZLatexWordPart(character) ||
				isZUnicodeWordPart(character);
	}
	
	public static boolean isZLatexWordPart(char character) {
		return Character.isLetterOrDigit(character) ||
				(character == '_') ||
				(character == '?') ||
				(character == '!') ||
				(character == '\\');
	}
	
	public static boolean isZUnicodeWordPart(char character) {
		return Character.isLetterOrDigit(character) ||
				(character =='?') || (character == '!') ||
				(character == '\'');
	}
	
	public static boolean isZLatexWhitespace(char character) {
		return Character.isWhitespace(character);
	}
	
	public static boolean isZUnicodeWhitespace(char character) {
		return Character.isWhitespace(character);
	}

}
