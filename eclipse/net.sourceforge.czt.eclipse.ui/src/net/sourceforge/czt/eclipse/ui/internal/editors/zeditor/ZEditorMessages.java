/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors.zeditor;

import java.util.ResourceBundle;

import org.eclipse.osgi.util.NLS;

/**
 * @author Chengdong
 *
 */
public final class ZEditorMessages extends NLS
{
  private static final String BUNDLE_FOR_ACTION_KEYS = "net.sourceforge.czt.eclipse.ui.internal.editors.actions.EditorActionMessages";//$NON-NLS-1$

  private static ResourceBundle fgBundleForActionKeys = ResourceBundle
      .getBundle(BUNDLE_FOR_ACTION_KEYS);

  /**
   * Returns the message bundle which contains constructed keys.
   *
   * @since 3.1
   * @return the message bundle
   */
  public static ResourceBundle getBundleForActionKeys()
  {
    return fgBundleForActionKeys;
  }

  private static final String BUNDLE_NAME = ZEditorMessages.class.getName();

  private ZEditorMessages()
  {
    // Do not instantiate
  }

  public static String Editor_FoldingMenu_label;

  public static String Editor_HighlightMenu_label;

  public static String Editor_ConvertMenu_label;

  public static String GotoMatchingBracket_label;

  public static String GotoMatchingBracket_error_invalidSelection;

  public static String GotoMatchingBracket_error_noMatchingBracket;

  public static String GotoMatchingBracket_error_bracketOutsideSelectedElement;

  public static String SemanticHighlighting_job;

  public static String SemanticHighlighting_field;

  public static String SemanticHighlighting_methodDeclaration;

  public static String SemanticHighlighting_localVariableDeclaration;

  public static String SemanticHighlighting_localVariable;

  public static String SemanticHighlighting_typeVariables;

  public static String SemanticHighlighting_method;

  public static String CZTEditor_markOccurrences_job_name;

  static {
    NLS.initializeMessages(BUNDLE_NAME, ZEditorMessages.class);
  }

}
