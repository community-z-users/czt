/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import org.eclipse.osgi.util.NLS;

/**
 * @author Chengdong Xu
 */
public final class PreferencesMessages extends NLS
{

  private static final String BUNDLE_NAME = "net.sourceforge.czt.eclipse.ui.internal.preferences.PreferencesMessages";//$NON-NLS-1$

  private PreferencesMessages()
  {
    // Do not instantiate
  }

  /*
   * Titles related information in basic preferences page for CZT development
   */
  public static String CZTBasePreferencePage_description;

  /*
   * Titles related information in compiler preferences page
   */
  public static String CompilerPreferencePage_description;
  public static String CompilerPreferencePage_properties;
  public static String CompilerPreferencePage_ignore_unknown_latex_commands;
  public static String CompilerPreferencePage_ignore_unknown_latex_commands_tooltip;
  public static String CompilerPreferencePage_typecheck_recursive_types;
  public static String CompilerPreferencePage_typecheck_recursive_types_tooltip;
  public static String CompilerPreferencePage_typecheck_use_strong_typing;
  public static String CompilerPreferencePage_typecheck_use_strong_typing_tooltip;
  
  
  /*
   * Titles related information in basic editor preferences page
   */
  public static String ZEditorBasePreferencePage_description;
  public static String ZEditorBasePreferencePage_note_link;
  public static String ZEditorBasePreferencePage_note_link_tooltip;
  public static String ZEditorBasePreferencePage_parsing_enable;
  public static String ZEditorBasePreferencePage_parsing_enable_tooltip;
  public static String ZEditorBasePreferencePage_report_problems_on_save;
  public static String ZEditorBasePreferencePage_report_problems_while_editing;
  public static String ZEditorBasePreferencePage_compiler_link;
  public static String ZEditorBasePreferencePage_compiler_link_tooltip;
  public static String ZEditorBasePreferencePage_matching_brackets;
  public static String ZEditorBasePreferencePage_matching_brackets_color;
  public static String ZEditorBasePreferencePage_sync_outline_on_cursor_move;
  
  /*
   * Editor hover preferences settings
   */
  public static String ZEditorBasePreferencePage_show_text_hover;
  
  /*
   * Titles related information for marking occurrences settings
   */
  public static String ZEditorBasePreferencePage_mark_occurrences;
  public static String ZEditorBasePreferencePage_sticky_occurrences;
  
  //  public static String ZEditorPreferencePage_selectionBackgroundColor;

  //  public static String ZEditorPreferencePage_selectionForegroundColor;
  
  
  /*
   * Titles related information in annotation preference page
   */ 
  public static String ZEditorPreferencePage_annotation_description;
  public static String ZEditorPreferencePage_annotation_note_link;
  public static String ZEditorPreferencePage_annotation_note_link_tooltip;
  public static String ZEditorPreferencePage_annotation_schema_box;
  public static String ZEditorPreferencePage_annotation_schema_box_enable;
  public static String ZEditorPreferencePage_annotation_schema_box_style;
  public static String ZEditorPreferencePage_annotation_schema_box_style_1;
  public static String ZEditorPreferencePage_annotation_schema_box_style_2;
  public static String ZEditorPreferencePage_annotation_schema_box_line_color;
  public static String ZEditorPreferencePage_annotation_schema_box_line_width;
  
  /*
   * Titles related information in folding preferences page
   */
  public static String ZEditorPreferencePage_folding_description;
  public static String ZEditorPreferencePage_folding_enable;
  public static String ZEditorPreferencePage_folding_enable_tooltip;
  public static String ZEditorPreferencePage_folding_enable_elements;
  public static String ZEditorPreferencePage_folding_element_narrative;
  public static String ZEditorPreferencePage_folding_element_directive;
  public static String ZEditorPreferencePage_folding_element_zed;
  public static String ZEditorPreferencePage_folding_element_section;
  public static String ZEditorPreferencePage_folding_element_ax;
  public static String ZEditorPreferencePage_folding_element_sch;
  public static String ZEditorPreferencePage_folding_element_genax;
  public static String ZEditorPreferencePage_folding_element_gensch;
  public static String ZEditorPreferencePage_folding_element_theorem;
  public static String ZEditorPreferencePage_folding_element_proofscript;
  
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

  public static String CompilerPreferencePage_dialect_tooltip;
  
  /*    
   public static String JavaBasePreferencePage_doubleclick_action;
   public static String JavaBasePreferencePage_doubleclick_gointo;
   public static String JavaBasePreferencePage_doubleclick_expand;
   public static String JavaEditorPreferencePage_showOverviewRuler;
   public static String JavaEditorPreferencePage_highlightMatchingBrackets;
   public static String JavaEditorPreferencePage_highlightCurrentLine;
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
   */
  static {
    NLS.initializeMessages(BUNDLE_NAME, PreferencesMessages.class);
  }
}
