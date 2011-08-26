package net.sourceforge.czt.eclipse.preferences;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.util.IZColorConstants;
import net.sourceforge.czt.parser.util.ParsePropertiesKeys;
import net.sourceforge.czt.typecheck.z.TypecheckPropertiesKeys;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.RGB;

/**
 * Preference constants used in the CZT preference store. Clients should only read the
 * CZT preference store using these values. Clients are not allowed to modify the 
 * preference store programmatically.
 * 
 * @author Chengdong Xu
 */
public class PreferenceConstants
{
  private PreferenceConstants()
  {
  }

  /*
   * Compiler preference keys
   */

  /**
   * A named preference that determines the parser and typechecker
   * that are used for all CZT buffers.
   * <p>
   * Value can be "z", "oz", "circus" etc.
   * </p>
   */
  public static final String PROP_DIALECT = "czt_dialect";
  
  /**
   * A named preference that sets the property of the parser.
   * <p>
   * Value is of type <code>boolean</code>.
   * </p>
   * <p>
   * When set to <code>true</code>, the parser tools will ignore
   * unknown latex commands (that is, give a warning and use the name
   * of the command) instead of reporting an error.  Reporting an
   * error is Standard conforming but ignoring those unknown commands
   * is sometimes convenient.
   * </p>
   */
  public static final String PROP_IGNORE_UNKNOWN_LATEX_COMMANDS = ParsePropertiesKeys.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS; 

  /**
   * A named preference that sets the property of the typechecker for z and oz.
   * <p>
   * Value is of type <code>boolean</code>.
   * </p>
   * <p>
   * When this property is <code>true</code>, the typechecker
   * will check that names are declared before they are used.
   * </p>
   */
  public static final String PROP_TYPECHECK_RECURSIVE_TYPES = TypecheckPropertiesKeys.PROP_TYPECHECK_RECURSIVE_TYPES; 

  /**
   * A named preference that sets the property of the typechecker for oz.
   * <p>
   * Value is of type <code>boolean</code>.
   * </p>
   * <p>
   * When this property is <code>true</code>, the typechecker
   * will check using strong typing.
   * </p>
   */
  public static final String PROP_TYPECHECK_USE_STRONG_TYPING = net.sourceforge.czt.typecheck.oz.TypecheckPropertiesKeys.PROP_TYPECHECK_USE_STRONG_TYPING; 

  private static final String EDITOR_PREF = CZTPlugin.getPluginID() + ".editor";
  private static final String ANNOTATION_PREF = EDITOR_PREF + ".annotation";
  
  /*
   * Editor base preference keys
   */
  /**
   * A named preference that controls whether parsing is turned on or off in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_PARSING_ENABLED = EDITOR_PREF + ".parsing_enabled"; //$NON-NLS-1$

  /**
   * A named preference that controls whether the editor reports problems from parsing
   * and update its correcsponding views while editing or when saving the content
   * of an CZT editor. 
   * <p>
   * Value is of type <code>String</code>: possible values are <code>
   * UPDATE_ON_SAVE</code> or <code>
   * UPDATE_WHILE_EDITING</code>.
   * </p>
   * 
   * @see #EDITOR_REPORT_PROBLEMS_ON_SAVE
   * @see #EDITOR_REPORT_PROBLEMS_WHILE_EDITING
   */
  public static final String EDITOR_REPORT_PROBLEMS = EDITOR_PREF + ".report.problems"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>EDITOR_REPORT_PROBLEMS</code>
   * 
   * @see #EDITOR_REPORT_PROBLEMS
   */
  public static final String EDITOR_REPORT_PROBLEMS_ON_SAVE = EDITOR_PREF + ".report.problems.OnSave"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>EDITOR_REPORT_PROBLEMS</code>
   * 
   * @see #EDITOR_REPORT_PROBLEMS
   */
  public static final String EDITOR_REPORT_PROBLEMS_WHILE_EDITING = EDITOR_PREF + ".report.problems.WhileEditing"; //$NON-NLS-1$

  /**
   * A named preference that controls whether bracket matching highlighting is turned on or off.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_MATCHING_BRACKETS = EDITOR_PREF + ".MatchingBrackets"; //$NON-NLS-1$

  /**
   * A named preference that holds the color used to highlight matching brackets.
   * <p>
   * Value is of type <code>String</code>. A RGB color value encoded as a string 
   * using class <code>PreferenceConverter</code>
   * </p>
   * 
   * @see org.eclipse.jface.resource.StringConverter
   * @see org.eclipse.jface.preference.PreferenceConverter
   */
  public final static String EDITOR_MATCHING_BRACKETS_COLOR = EDITOR_PREF + ".MatchingBracketsColor"; //$NON-NLS-1$

  /**
   * A named preference that controls whether the outline view selection
   * should stay in sync with with element at the current cursor position.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE = EDITOR_PREF + ".SyncOutlineOnCursorMove"; //$NON-NLS-1$
  
  /*
   * Hover preference keys
   */
  /**
   * A named preference that controls whether hover tool tips in the Z editor are turned on or off.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_SHOW_HOVER = EDITOR_PREF + ".showHover"; //$NON-NLS-1$

  /**
   * A named preference that controls whether annotation roll over is used or not.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true<code> the annotation ruler column
   * uses a roll over to display multiple annotations
   * </p>
   */
  public static final String EDITOR_ANNOTATION_ROLL_OVER = ANNOTATION_PREF + ".rollover"; //$NON-NLS-1$

  /*
   * Mark occurrence preference keys
   */
  /**
   * A named preference that controls whether occurrences are marked in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_MARK_OCCURRENCES = EDITOR_PREF + ".MarkOccurrences"; //$NON-NLS-1$

  /**
   * A named preference that controls whether occurrences are sticky in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_STICKY_OCCURRENCES = EDITOR_PREF + ".StickyOccurrences"; //$NON-NLS-1$

  /*
   * Annotation preference keys
   */
  /**
   * A named preference that controls whether the editor draws schema boxes.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_ENABLE = ANNOTATION_PREF + ".schemabox.enable";
  
  /**
   * A named preference that controls the style that the editor uses to draw the schema boxes. 
   * <p>
   * Value is of type <code>String</code>: possible values are <code>
   * EDITOR_ANNOTATION_SCHEMABOX_STYLE_1</code> or <code>
   * EDITOR_ANNOTATION_SCHEMABOX_STYLE_2</code>.
   * </p>
   * 
   * @see #EDITOR_ANNOTATION_SCHEMABOX_STYLE_1
   * @see #EDITOR_ANNOTATION_SCHEMABOX_STYLE_2
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_STYLE = ANNOTATION_PREF + ".schemabox.style";
  
  /**
   * A string value used by the named preference <code>EDITOR_ANNOTATION_SCHEMABOX_STYLE</code>
   * 
   * @see #EDITOR_ANNOTATION_SCHEMABOX_STYLE
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_STYLE_1 = ANNOTATION_PREF + ".schemabox.style_1";
  
  /**
   * A string value used by the named preference <code>EDITOR_ANNOTATION_SCHEMABOX_STYLE</code>
   * 
   * @see #EDITOR_ANNOTATION_SCHEMABOX_STYLE
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_STYLE_2 = ANNOTATION_PREF + ".schemabox.style_2";
  
  /**
   * A named preference that holds the color used to draw schema boxes.
   * <p>
   * Value is of type <code>String</code>. A RGB color value encoded as a string 
   * using class <code>PreferenceConverter</code>
   * </p>
   * 
   * @see org.eclipse.jface.resource.StringConverter
   * @see org.eclipse.jface.preference.PreferenceConverter
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_LINE_COLOR = ANNOTATION_PREF + ".schemabox.line_color";
  
  /**
   * A named preference that holds the width used to draw schema boxes.
   * <p>
   * Value is of type <code>int</code>.
   * </p>
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_LINE_WIDTH = ANNOTATION_PREF + ".schemabox.line_width";
  
  /*
   * Folding preference keys
   */
  /**
   * A named preference that controls whether folding is enabled in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_ENABLED = EDITOR_PREF + ".folding.enabled"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * narrative section/paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_NARRATIVE = EDITOR_PREF + ".folding_narrative"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * directive paragraph (%%zchar).
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_ZCHAR = EDITOR_PREF + ".folding_ZCHAR"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * ZED.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_ZED = EDITOR_PREF + ".folding_zed"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * section header paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_ZSECTION = EDITOR_PREF + ".folding_zsection"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * axiomatic description paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_AX = EDITOR_PREF + ".folding_ax"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * schema definition paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_SCH = EDITOR_PREF + ".folding_sch"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * generic axiomatic description paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_GENAX = EDITOR_PREF + ".folding_genax"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * generic schema definition paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_GENSCH = EDITOR_PREF + ".folding_gensch"; //$NON-NLS-1$

  
  /**
   * A named preference that controls whether the editor folds theorem paragraphs.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_THEOREM = EDITOR_PREF + ".folding_theorem"; //$NON-NLS-1$
  
  
  /**
   * A named preference that controls whether the editor folds proof script paragraphs.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_PROOFSCRIPT = EDITOR_PREF + ".folding_proofscript"; //$NON-NLS-1$
  
  /*
   * Syntax coloring preference keys
   */

  /**
   * Preference key suffix for foreground text color preference keys
   */
  public static final String EDITOR_FOREGROUND_SUFFIX = "_foreground";

  /**
   * Preference key suffix for bold text style preference keys.
   */
  public static final String EDITOR_BOLD_SUFFIX = "_bold"; //$NON-NLS-1$

  /**
   * Preference key suffix for italic text style preference keys.
   */
  public static final String EDITOR_ITALIC_SUFFIX = "_italic"; //$NON-NLS-1$

  /**
   * Preference key suffix for strikethrough text style preference keys.
   */
  public static final String EDITOR_STRIKETHROUGH_SUFFIX = "_strikethrough"; //$NON-NLS-1$

  /**
   * Preference key suffix for underline text style preference keys.
   */
  public static final String EDITOR_UNDERLINE_SUFFIX = "_underline"; //$NON-NLS-1$

  /**
   * The symbolic font name for the Java fEditor text font 
   * (value <code>"org.eclipse.jdt.ui.editors.textfont"</code>).
   */
  public final static String EDITOR_TEXT_FONT = "org.eclipse.jdt.ui.editors.textfont"; //$NON-NLS-1$
  
  /**
   * The symbolic font name for Z Editor font when editing Unicode specifications
   */
  public final static String EDITOR_UNICODE_FONT = EDITOR_PREF + ".font.unicode"; //$NON-NLS-1$
  
  /**
   * The symbolic font name for Z Editor font when editing LaTeX specifications
   */
  public final static String EDITOR_LATEX_FONT = EDITOR_PREF + ".font.latex"; //$NON-NLS-1$

  /**
   * A named preference that holds the color used to render narrative paragraphs.
   * <p>
   * Value is of type <code>String</code>. A RGB color value encoded as a string
   * using class <code>PreferenceConverter</code>
   * </p>
   * 
   * @see org.eclipse.jface.resource.StringConverter
   * @see org.eclipse.jface.preference.PreferenceConverter
   */
  public final static String EDITOR_Z_NARRATIVE_FOREGROUND = IZColorConstants.CZT_NARRATIVE
      + EDITOR_FOREGROUND_SUFFIX;

  /**
   * A named preference that controls whether narrative paragraphs are rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in bold. If <code>false</code> the are rendered using no font style attribute.
   * </p>
   */
  public final static String EDITOR_Z_NARRATIVE_BOLD = IZColorConstants.CZT_NARRATIVE
      + EDITOR_BOLD_SUFFIX;

  /**
   * A named preference that controls whether narrative paragraphs are rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in italic. If <code>false</code> the are rendered using no italic font style attribute.
   * </p>
   */
  public final static String EDITOR_Z_NARRATIVE_ITALIC = IZColorConstants.CZT_NARRATIVE
      + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether narrative paragraphs are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in strikethrough. If <code>false</code> the are rendered using no strikethrough font style attribute.
   * </p>
   */
  public final static String EDITOR_Z_NARRATIVE_STRIKETHROUGH = IZColorConstants.CZT_NARRATIVE
      + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether narrative paragraphs are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in underline. If <code>false</code> the are rendered using no underline font style attribute.
   * </p>
   */
  public final static String EDITOR_Z_NARRATIVE_UNDERLINE = IZColorConstants.CZT_NARRATIVE
      + EDITOR_UNDERLINE_SUFFIX;

  /**
   * A named preference that holds the color used to render single-line comments foreground.
   * <p>
   * Value is of type <code>String</code>. A RGB color value encoded as a string
   * using class <code>PreferenceConverter</code>
   * </p>
   * 
   * @see org.eclipse.jface.resource.StringConverter
   * @see org.eclipse.jface.preference.PreferenceConverter
   */
  public final static String EDITOR_Z_COMMENT_FOREGROUND = IZColorConstants.CZT_COMMENT
      + EDITOR_FOREGROUND_SUFFIX;

  /**
   * A named preference that controls whether single-line comments are rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in bold. If <code>false</code> the are rendered using no font style attribute.
   * </p>
   */
  public final static String EDITOR_Z_COMMENT_BOLD = IZColorConstants.CZT_COMMENT
      + EDITOR_BOLD_SUFFIX;

  /**
   * A named preference that controls whether single-line comments are rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in italic. If <code>false</code> the are rendered using no italic font style attribute.
   * </p>
   */
  public final static String EDITOR_Z_COMMENT_ITALIC = IZColorConstants.CZT_COMMENT
      + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether single-line comments are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in strikethrough. If <code>false</code> the are rendered using no strikethrough font style attribute.
   * </p>
   */
  public final static String EDITOR_Z_COMMENT_STRIKETHROUGH = IZColorConstants.CZT_COMMENT
      + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether single-line comments are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in underline. If <code>false</code> the are rendered using no underline font style attribute.
   * </p>
   */
  public final static String EDITOR_Z_COMMENT_UNDERLINE = IZColorConstants.CZT_COMMENT
      + EDITOR_UNDERLINE_SUFFIX;

  /**
   * A named preference that holds the color used to render Z keywords.
   * <p>
   * Value is of type <code>String</code>. A RGB color value encoded as a string
   * using class <code>PreferenceConverter</code>
   * </p>
   * 
   * @see org.eclipse.jface.resource.StringConverter
   * @see org.eclipse.jface.preference.PreferenceConverter
   */
  public final static String EDITOR_Z_KEYWORD_FOREGROUND = IZColorConstants.CZT_KEYWORD
      + EDITOR_FOREGROUND_SUFFIX;

  /**
   * A named preference that controls whether keywords are rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_KEYWORD_BOLD = IZColorConstants.CZT_KEYWORD
      + EDITOR_BOLD_SUFFIX;

  /**
   * A named preference that controls whether keywords are rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_KEYWORD_ITALIC = IZColorConstants.CZT_KEYWORD
      + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether keywords are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_KEYWORD_STRIKETHROUGH = IZColorConstants.CZT_KEYWORD
      + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether keywords are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_KEYWORD_UNDERLINE = IZColorConstants.CZT_KEYWORD
      + EDITOR_UNDERLINE_SUFFIX;

  /**
   * A named preference that holds the color used to render Z operators.
   * <p>
   * Value is of type <code>String</code>. A RGB color value encoded as a string
   * using class <code>PreferenceConverter</code>
   * </p>
   * 
   * @see org.eclipse.jface.resource.StringConverter
   * @see org.eclipse.jface.preference.PreferenceConverter
   */
  public final static String EDITOR_Z_OPERATOR_FOREGROUND = IZColorConstants.CZT_OPERATOR
      + EDITOR_FOREGROUND_SUFFIX;

  /**
   * A named preference that controls whether operators are rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_OPERATOR_BOLD = IZColorConstants.CZT_OPERATOR
      + EDITOR_BOLD_SUFFIX;

  /**
   * A named preference that controls whether operators are rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_OPERATOR_ITALIC = IZColorConstants.CZT_OPERATOR
      + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether operators are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_OPERATOR_STRIKETHROUGH = IZColorConstants.CZT_OPERATOR
      + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether operators are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_OPERATOR_UNDERLINE = IZColorConstants.CZT_OPERATOR
      + EDITOR_UNDERLINE_SUFFIX;

  /**
   * A named preference that holds the color used to render Z default text.
   * <p>
   * Value is of type <code>String</code>. A RGB color value encoded as a string
   * using class <code>PreferenceConverter</code>
   * </p>
   * 
   * @see org.eclipse.jface.resource.StringConverter
   * @see org.eclipse.jface.preference.PreferenceConverter
   */
  public final static String EDITOR_Z_DEFAULT_FOREGROUND = IZColorConstants.CZT_DEFAULT
      + EDITOR_FOREGROUND_SUFFIX;

  /**
   * A named preference that controls whether Z default text is rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_DEFAULT_BOLD = IZColorConstants.CZT_DEFAULT
      + EDITOR_BOLD_SUFFIX;

  /**
   * A named preference that controls whether Z default text is rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_DEFAULT_ITALIC = IZColorConstants.CZT_DEFAULT
      + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether Z default text is rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_DEFAULT_STRIKETHROUGH = IZColorConstants.CZT_DEFAULT
      + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether Z default text is rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_Z_DEFAULT_UNDERLINE = IZColorConstants.CZT_DEFAULT
      + EDITOR_UNDERLINE_SUFFIX;

  /*
   * Z Character view preference keys
   */
  /**
   * A named preference that controls the way in which a zchar is inserted in the charmap view. 
   * <p>
   * Value is of type <code>String</code>: possible values are <code>
   * INSERT_ZCHAR_BY_CLICK</code> or <code>
   * INSERT_ZCHAR_BY_DOUBLE_CLICK</code>.
   * </p>
   * 
   * @see #DOUBLE_CLICK_EXPANDS
   * @see #DOUBLE_CLICK_GOES_INTO
   */
  public static final String INSERT_ZCHAR = "net.sourceforge.czt.eclipse.charmapview.InsertZChar"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>SINGLE_CLICK</code>.
   * 
   * @see #CLICK
   */
  public static final String INSERT_ZCHAR_BY_CLICK = "net.sourceforge.czt.eclipse.charmapview.SingleClick"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>DOUBLE_CLICK</code>.
   * 
   * @see #DOUBLE_CLICK
   */
  public static final String INSERT_ZCHAR_BY_DOUBLE_CLICK = "net.sourceforge.czt.eclipse.charmapview.DoubleClick"; //$NON-NLS-1$

  
  /**
   * A named preference that controls whether the complete syntax tree is displayed in the
   * editor outline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String OUTLINE_Z_COMPLETE_TREE = "net.sourceforge.czt.eclipse.outline.completeTree"; //$NON-NLS-1$
  
  /**
   * Initializes the given preference store with the default values.
   * 
   * @param store the preference store to be initialized
   */
  public static void initializeDefaultValues(IPreferenceStore store)
  {

    // CZT base preference page
    //		store.setDefault(PreferenceConstants.DOUBLE_CLICK, PreferenceConstants.DOUBLE_CLICK_EXPANDS);
    //		store.setDefault(PreferenceConstants.UPDATE_Z_VIEWS, PreferenceConstants.UPDATE_WHILE_EDITING);	
    //		store.setToDefault(PreferenceConstants.UPDATE_Z_VIEWS); // clear preference, update on save not supported anymore

    //		store.setDefault(PreferenceConstants.SEARCH_USE_REDUCED_MENU, true);
    // Appearance preference page
    //		store.setDefault(PreferenceConstants.APPEARANCE_PKG_NAME_PATTERN_FOR_PKG_VIEW, ""); //$NON-NLS-1$
    //		store.setDefault(PreferenceConstants.APPEARANCE_FOLD_PACKAGES_IN_PACKAGE_EXPLORER, true);

    // Compiler preference page
    store.setDefault(PROP_DIALECT, "z");
    
    store.setDefault(PROP_IGNORE_UNKNOWN_LATEX_COMMANDS, 
        ParsePropertiesKeys.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS_DEFAULT);

    store.setDefault(PROP_TYPECHECK_RECURSIVE_TYPES, 
        TypecheckPropertiesKeys.PROP_TYPECHECK_RECURSIVE_TYPES_DEFAULT);

    store.setDefault(PROP_TYPECHECK_USE_STRONG_TYPING, 
        net.sourceforge.czt.typecheck.oz.TypecheckPropertiesKeys.PROP_TYPECHECK_USE_STRONG_TYPING_DEFAULT);

    // Editor base preference page
    store.setDefault(EDITOR_PARSING_ENABLED, true);
    store.setDefault(EDITOR_REPORT_PROBLEMS, EDITOR_REPORT_PROBLEMS_WHILE_EDITING);
    store.setDefault(EDITOR_MATCHING_BRACKETS, true);
    PreferenceConverter.setDefault(store, EDITOR_MATCHING_BRACKETS_COLOR, new RGB(192, 192, 192));
    store.setDefault(EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE, true);
    store.setDefault(EDITOR_SHOW_HOVER, true);
//    store.setDefault(EDITOR_ANNOTATION_ROLL_OVER, true);
    store.setDefault(EDITOR_MARK_OCCURRENCES, true);
//    store.setDefault(EDITOR_STICKY_OCCURRENCES, true);
    
    // Editor annotation preference page
    store.setDefault(EDITOR_ANNOTATION_SCHEMABOX_ENABLE, true);
    store.setDefault(EDITOR_ANNOTATION_SCHEMABOX_STYLE, EDITOR_ANNOTATION_SCHEMABOX_STYLE_2);
    PreferenceConverter.setDefault(store, EDITOR_ANNOTATION_SCHEMABOX_LINE_COLOR, new RGB(255, 100, 100));
    store.setDefault(EDITOR_ANNOTATION_SCHEMABOX_LINE_WIDTH, 0);


    //  Folding preference page
    store.setDefault(EDITOR_FOLDING_ENABLED, true);
    store.setDefault(EDITOR_FOLDING_NARRATIVE, true);
    store.setDefault(EDITOR_FOLDING_ZCHAR, true);
    store.setDefault(EDITOR_FOLDING_ZED, true);
    store.setDefault(EDITOR_FOLDING_ZSECTION, true);
    store.setDefault(EDITOR_FOLDING_AX, true);
    store.setDefault(EDITOR_FOLDING_SCH, true);
    store.setDefault(EDITOR_FOLDING_GENAX, true);
    store.setDefault(EDITOR_FOLDING_GENSCH, true);
    store.setDefault(EDITOR_FOLDING_THEOREM, true);
    store.setDefault(EDITOR_FOLDING_PROOFSCRIPT, true);
    
    // Syntax coloring preference page
    PreferenceConverter.setDefault(store, EDITOR_Z_NARRATIVE_FOREGROUND, new RGB(128, 0, 0));
    store.setDefault(EDITOR_Z_NARRATIVE_BOLD, false);
    store.setDefault(EDITOR_Z_NARRATIVE_ITALIC, false);

    PreferenceConverter.setDefault(store, EDITOR_Z_COMMENT_FOREGROUND, new RGB(128, 128, 0));
    store.setDefault(EDITOR_Z_COMMENT_BOLD, false);
    store.setDefault(EDITOR_Z_COMMENT_ITALIC, false);

    PreferenceConverter.setDefault(store, EDITOR_Z_KEYWORD_FOREGROUND, new RGB(64, 64, 128));
    store.setDefault(EDITOR_Z_KEYWORD_BOLD, true);
    store.setDefault(EDITOR_Z_KEYWORD_ITALIC, false);

    PreferenceConverter.setDefault(store, EDITOR_Z_OPERATOR_FOREGROUND, new RGB(64, 64, 128));
    store.setDefault(EDITOR_Z_OPERATOR_BOLD, true);
    store.setDefault(EDITOR_Z_OPERATOR_ITALIC, false);

    PreferenceConverter.setDefault(store, EDITOR_Z_DEFAULT_FOREGROUND, new RGB(0, 0, 0));
    store.setDefault(EDITOR_Z_DEFAULT_BOLD, false);
    store.setDefault(EDITOR_Z_DEFAULT_ITALIC, false);
    
    store.setDefault(OUTLINE_Z_COMPLETE_TREE, false);

  }

  /**
   * Returns the CZT preference store.
   * 
   * @return the CZT preference store
   */
  public static IPreferenceStore getPreferenceStore()
  {
    return CZTPlugin.getDefault().getPreferenceStore();
  }

}
