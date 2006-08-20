/**
 * 
 */
package net.sourceforge.czt.eclipse.editors.actions;

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
   * Action definition ID of the edit -> go to matching bracket action
   * (value <code>"org.eclipse.jdt.ui.edit.text.java.goto.matching.bracket"</code>).
   *
   * @since 2.1
   */
  public static final String GOTO_MATCHING_BRACKET= "org.eclipse.jdt.ui.edit.text.java.goto.matching.bracket"; //$NON-NLS-1$

  /**
   * Action definition ID of the edit -> go to next member action
   * (value <code>"org.eclipse.jdt.ui.edit.text.java.goto.next.member"</code>).
   *
   * @since 2.1
   */
  public static final String GOTO_NEXT_MEMBER= "org.eclipse.jdt.ui.edit.text.java.goto.next.member"; //$NON-NLS-1$

  /**
   * Action definition ID of the edit -> go to previous member action
   * (value <code>"org.eclipse.jdt.ui.edit.text.java.goto.previous.member"</code>).
   *
   * @since 2.1
   */
  public static final String GOTO_PREVIOUS_MEMBER= "org.eclipse.jdt.ui.edit.text.java.goto.previous.member"; //$NON-NLS-1$
  
  /**
   * Action definition ID of the edit -> select enclosing action
   * (value <code>"org.eclipse.jdt.ui.edit.text.java.select.enclosing"</code>).
   */
  public static final String SELECT_ENCLOSING= "org.eclipse.jdt.ui.edit.text.java.select.enclosing"; //$NON-NLS-1$
  
  /**
   * Action definition ID of the edit -> select next action
   * (value <code>"org.eclipse.jdt.ui.edit.text.java.select.next"</code>).
   */
  public static final String SELECT_NEXT= "org.eclipse.jdt.ui.edit.text.java.select.next"; //$NON-NLS-1$
  
  /**
   * Action definition ID of the edit -> select previous action
   * (value <code>"org.eclipse.jdt.ui.edit.text.java.select.previous"</code>).
   */
  public static final String SELECT_PREVIOUS= "org.eclipse.jdt.ui.edit.text.java.select.previous"; //$NON-NLS-1$
  
  /**
   * Action definition ID of the edit -> select restore last action
   * (value <code>"org.eclipse.jdt.ui.edit.text.java.select.last"</code>).
   */
  public static final String SELECT_LAST= "org.eclipse.jdt.ui.edit.text.java.select.last"; //$NON-NLS-1$
  
  public static final String GO_TO_DECLARATION = "net.sourceforge.czt.eclipse.editoraction.gotodeclaration";
  public static final String HIGHLIGHT_ENCLOSING_ELEMENT = "net.sourceforge.czt.eclipse.editoraction.expandselection";
  public static final String RESTORE_LAST_HIGHLIGHT = "net.sourceforge.czt.eclipse.editoraction.contractselection";
  public static final String CONVERT_TO_LATEX = "net.sourceforge.czt.eclipse.editoraction.convert2latex";
  public static final String CONVERT_TO_OLD_LATEX = "net.sourceforge.czt.eclipse.editoraction.convert2oldlatex";
  public static final String CONVERT_TO_UNICODE = "net.sourceforge.czt.eclipse.editoraction.convert2unicode";
  public static final String CONVERT_TO_XML = "net.sourceforge.czt.eclipse.editoraction.convert2xml";
  
}
