/**
 * 
 */

package net.sourceforge.czt.eclipse.preferences;

import org.eclipse.osgi.util.NLS;

/**
 * @author Chengdong Xu
 */
public final class PreferencesMessages extends NLS
{

  private static final String BUNDLE_NAME = "net.sourceforge.czt.eclipse.preferences.PreferencesMessages";//$NON-NLS-1$

  private PreferencesMessages()
  {
    // Do not instantiate
  }

  /*
   * Basic preferences settings for CZT development
   */
  public static String CZTBasePreferencePage_description;

  public static String AppearancePreferencePage_description;

  public static String ZEditorPreferencePage_selectionBackgroundColor;

  public static String ZEditorPreferencePage_selectionForegroundColor;

  public static String ZEditorPreferencePage_folding_title;

  public static String MarkOccurrencesConfigurationBlock_title;

  public static String MarkOccurrencesConfigurationBlock_markOccurrences;

  public static String MarkOccurrencesConfigurationBlock_stickyOccurrences;

  public static String MarkOccurrencesConfigurationBlock_markOccurrencesWhenExpansion;

  /*
   * Titles related information in syntax coloring preference page
   */
  public static String ZEditorColoringConfigurationBlock_link;

  public static String ZEditorPreferencePage_colors;

  public static String ZEditorPreferencePage_coloring_element;
  
  /*
   * Token names in syntax coloring preference page
   */
  public static String ZEditorPreferencePage_coloring_category_code;

  public static String ZEditorPreferencePage_keywords;

  public static String ZEditorPreferencePage_operators;
  
  public static String ZEditorPreferencePage_default;

  public static String ZEditorPreferencePage_comments;
  
  public static String ZEditorPreferencePage_narratives;
  
  /*
   * Labels in syntax coloring preference page
   */
  public static String ZEditorPreferencePage_enable;

  public static String ZEditorPreferencePage_foreground;

  public static String ZEditorPreferencePage_bold;

  public static String ZEditorPreferencePage_italic;

  public static String ZEditorPreferencePage_strikethrough;

  public static String ZEditorPreferencePage_underline;

  public static String ZEditorPreferencePage_preview;
  
  /*
   * Error information in editor preference pages
   */

  public static String ZEditorPreferencePage_empty_input;

  public static String ZEditorPreferencePage_invalid_input;
  /*    
   public static String JavaBasePreferencePage_doubleclick_action;
   public static String JavaBasePreferencePage_doubleclick_gointo;
   public static String JavaBasePreferencePage_doubleclick_expand;
   public static String JavaBasePreferencePage_refactoring_title;
   public static String JavaBasePreferencePage_refactoring_auto_save;
   public static String JavaBasePreferencePage_search;
   public static String JavaBasePreferencePage_search_small_menu;
   public static String NewJavaProjectPreferencePage_title;
   public static String NewJavaProjectPreferencePage_description;
   public static String NewJavaProjectPreferencePage_sourcefolder_label;
   public static String NewJavaProjectPreferencePage_sourcefolder_project;
   public static String NewJavaProjectPreferencePage_sourcefolder_folder;
   public static String NewJavaProjectPreferencePage_folders_src;
   public static String NewJavaProjectPreferencePage_folders_bin;
   public static String NewJavaProjectPreferencePage_folders_error_namesempty;
   public static String NewJavaProjectPreferencePage_folders_error_invalidsrcname;
   public static String NewJavaProjectPreferencePage_folders_error_invalidbinname;
   public static String NewJavaProjectPreferencePage_folders_error_invalidcp;
   public static String NewJavaProjectPreferencePage_error_decode;
   public static String JavaEditorPreferencePage_showOverviewRuler;
   public static String JavaEditorPreferencePage_highlightMatchingBrackets;
   public static String JavaEditorPreferencePage_highlightCurrentLine;
   public static String JavaEditorPreferencePage_enableAutoActivation;
   public static String JavaEditorPreferencePage_automaticallyAddImportInsteadOfQualifiedName;
   public static String JavaEditorPreferencePage_completionInserts;
   public static String JavaEditorPreferencePage_completionOverwrites;
   public static String JavaEditorPreferencePage_completionToggleHint;
   public static String JavaEditorPreferencePage_autoActivationDelay;
   public static String JavaEditorPreferencePage_autoActivationTriggersForJava;
   public static String JavaEditorPreferencePage_general;
   public static String ZEditorPreferencePage_colors;
   
   public static String JavaEditorPreferencePage_showLineNumbers;
   public static String JavaEditorPreferencePage_lineNumberForegroundColor;
   public static String JavaEditorPreferencePage_currentLineHighlighColor;
   public static String JavaBasePreferencePage_inView;
   public static String JavaBasePreferencePage_inPerspective;
   
   public static String FoldingConfigurationBlock_enable;
   public static String FoldingConfigurationBlock_combo_caption;
   public static String FoldingConfigurationBlock_info_no_preferences;
   public static String FoldingConfigurationBlock_error_not_exist;
   public static String ProjectSelectionDialog_title;
   public static String ProjectSelectionDialog_desciption;
   public static String ProjectSelectionDialog_filter;
   */
  static {
    NLS.initializeMessages(BUNDLE_NAME, PreferencesMessages.class);
  }

  public static String ProblemSeveritiesConfigurationBlock_pb_unhandled_surpresswarning_tokens;

  public static String ProblemSeveritiesConfigurationBlock_pb_enable_surpresswarning_annotation;

  public static String EditTemplateDialog_autoinsert;
}
