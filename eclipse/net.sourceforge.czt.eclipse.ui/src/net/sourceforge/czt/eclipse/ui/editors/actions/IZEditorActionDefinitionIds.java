/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.editors.actions;

import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;

/**
 * @author Chengdong
 *
 */
public interface IZEditorActionDefinitionIds
    extends
      ITextEditorActionDefinitionIds
{
  /**
   * Action definition ID of the edit -> go to declaraction action
   * (value <code>"net.sourceforge.czt.eclipse.editoraction.gotodeclaration"</code>).
   */
  public static final String GO_TO_DECLARATION = "net.sourceforge.czt.eclipse.editoraction.gotodeclaration";
  
  /**
   * Action definition ID of the edit -> highlight -> highlight enclosing action
   * (value <code>"net.sourceforge.czt.eclipse.editoraction.expandselection"</code>).
   */
  public static final String HIGHLIGHT_ENCLOSING_ELEMENT = "net.sourceforge.czt.eclipse.editoraction.expandselection";
  
  /**
   * Action definition ID of the edit -> highlight -> restore last highlight action
   * (value <code>"net.sourceforge.czt.eclipse.editoraction.contractselection"</code>).
   */
  public static final String RESTORE_LAST_HIGHLIGHT = "net.sourceforge.czt.eclipse.editoraction.contractselection";
  
  /**
   * Action definition ID of the edit -> convert to -> convert to LaTeX action
   * (value <code>"net.sourceforge.czt.eclipse.editoraction.convert2latex"</code>).
   */
  public static final String CONVERT_TO_LATEX = "net.sourceforge.czt.eclipse.editoraction.convert2latex";
  
  /**
   * Action definition ID of the edit -> convert to -> convert to old LaTeX action
   * (value <code>"net.sourceforge.czt.eclipse.editoraction.convert2oldlatex"</code>).
   */
  public static final String CONVERT_TO_OLD_LATEX = "net.sourceforge.czt.eclipse.editoraction.convert2oldlatex";
  
  /**
   * Action definition ID of the edit -> convert to -> convert to Unicode action
   * (value <code>"net.sourceforge.czt.eclipse.editoraction.convert2unicode"</code>).
   */
  public static final String CONVERT_TO_UNICODE = "net.sourceforge.czt.eclipse.editoraction.convert2unicode";
  
  /**
   * Action definition ID of the edit -> convert to -> convert to XML action
   * (value <code>"net.sourceforge.czt.eclipse.editoraction.convert2xml"</code>).
   */
  public static final String CONVERT_TO_XML = "net.sourceforge.czt.eclipse.editoraction.convert2xml";
  
  /**
   * Action definition ID of the edit -> go to matching bracket action
   * (value <code>"net.sourceforge.czt.eclipse.editoraction.gotomatchingbracket"</code>).
   */
  public static final String GOTO_MATCHING_BRACKET= "net.sourceforge.czt.eclipse.editoraction.gotomatchingbracket"; //$NON-NLS-1$

}
