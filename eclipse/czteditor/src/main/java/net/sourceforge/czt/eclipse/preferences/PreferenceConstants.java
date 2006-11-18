/**
 * 
 */

package net.sourceforge.czt.eclipse.preferences;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.util.IZColorConstants;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

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
   * A named preference that sets the property of the parser.
   * <p>
   * Value is of type <code>boolean</code>.
   * </p>
   * <p>
   * When set to <code>true</code>, the parser tools extract
   * symbol characters COMMA, SEMICOLON, and FULL STOP from the
   * beginning and end of a WORD token to become WORDs themselves.
   * This is a planned change to the Z Standard; see also
   * the Draft Technical Corrigendum 1: Corrections,
   * including to use of Unicode, March 17th, 2006.
   * As of now, this has yet to be submitted for official ballot.
   * </p>
   */
  public static final String PROP_EXTRACT_COMMA_OR_SEMI_FROM_DECORWORDS = net.sourceforge.czt.parser.util.ParsePropertiesKeys.PROP_EXTRACT_COMMA_OR_SEMI_FROM_DECORWORDS; //$NON-NLS-1$

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
  public static final String PROP_IGNORE_UNKNOWN_LATEX_COMMANDS = net.sourceforge.czt.parser.util.ParsePropertiesKeys.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS; //$NON-NLS-1$

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
  public static final String PROP_TYPECHECK_USE_BEFORE_DECL = net.sourceforge.czt.typecheck.z.TypecheckPropertiesKeys.PROP_TYPECHECK_USE_BEFORE_DECL; //$NON-NLS-1$

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
  public static final String PROP_TYPECHECK_USE_STRONG_TYPING = net.sourceforge.czt.typecheck.oz.TypecheckPropertiesKeys.PROP_TYPECHECK_USE_STRONG_TYPING; //$NON-NLS-1$

  /*
   * Editor base preference keys
   */
  /**
   * A named preference that controls whether parsing is turned on or off in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_PARSING_ENABLED = "editor_parsing_enabled"; //$NON-NLS-1$

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
  public static final String EDITOR_REPORT_PROBLEMS = "editor.report.problems"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>EDITOR_REPORT_PROBLEMS</code>
   * 
   * @see #EDITOR_REPORT_PROBLEMS
   */
  public static final String EDITOR_REPORT_PROBLEMS_ON_SAVE = "editor.report.problems.OnSave"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>EDITOR_REPORT_PROBLEMS</code>
   * 
   * @see #EDITOR_REPORT_PROBLEMS
   */
  public static final String EDITOR_REPORT_PROBLEMS_WHILE_EDITING = "editor.report.problems.WhileEditing"; //$NON-NLS-1$

  /**
   * A named preference that controls whether bracket matching highlighting is turned on or off.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_MATCHING_BRACKETS = "MatchingBrackets"; //$NON-NLS-1$

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
  public final static String EDITOR_MATCHING_BRACKETS_COLOR = "MatchingBracketsColor"; //$NON-NLS-1$

  /**
   * A named preference that controls whether the outline view selection
   * should stay in sync with with element at the current cursor position.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE = "editor.SyncOutlineOnCursorMove"; //$NON-NLS-1$
  
  /*
   * Hover preference keys
   */
  /**
   * A named preference that controls whether hover tool tips in the Z editor are turned on or off.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_SHOW_HOVER = "org.eclipse.jdt.ui.editor.showHover"; //$NON-NLS-1$

  /**
   * A named preference that controls whether annotation roll over is used or not.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true<code> the annotation ruler column
   * uses a roll over to display multiple annotations
   * </p>
   */
  public static final String EDITOR_ANNOTATION_ROLL_OVER = "editor_annotation_roll_over"; //$NON-NLS-1$

  /*
   * Mark occurrence preference keys
   */
  /**
   * A named preference that controls whether occurrences are marked in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_MARK_OCCURRENCES = "MarkOccurrences"; //$NON-NLS-1$

  /**
   * A named preference that controls whether occurrences are sticky in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_STICKY_OCCURRENCES = "StickyOccurrences"; //$NON-NLS-1$

  /**
   * A named preference that controls whether occurrences are marked
   * when a term is highlighted in the editor .
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_MARK_OCCURRENCES_WHEN_HIGHLIGHTING_TERM = "MarkOccurrencesWhenExpansion"; //$NON-NLS-1$

  /*
   * Annotation preference keys
   */
  /**
   * A named preference that controls whether the editor draws schema boxes.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_ENABLE = "editor_annotation_schemabox_enable";
  
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
  public final static String EDITOR_ANNOTATION_SCHEMABOX_STYLE = "editor_annotation_schemabox_style";
  
  /**
   * A string value used by the named preference <code>EDITOR_ANNOTATION_SCHEMABOX_STYLE</code>
   * 
   * @see #EDITOR_ANNOTATION_SCHEMABOX_STYLE
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_STYLE_1 = "editor_annotation_schemabox_style_1";
  
  /**
   * A string value used by the named preference <code>EDITOR_ANNOTATION_SCHEMABOX_STYLE</code>
   * 
   * @see #EDITOR_ANNOTATION_SCHEMABOX_STYLE
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_STYLE_2 = "editor_annotation_schemabox_style_2";
  
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
  public final static String EDITOR_ANNOTATION_SCHEMABOX_LINE_COLOR = "editor_annotation_schemabox_line_color";
  
  /**
   * A named preference that holds the width used to draw schema boxes.
   * <p>
   * Value is of type <code>int</code>.
   * </p>
   */
  public final static String EDITOR_ANNOTATION_SCHEMABOX_LINE_WIDTH = "editor_annotation_schemabox_line_width";
  
  /*
   * Folding preference keys
   */
  /**
   * A named preference that controls whether folding is enabled in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_ENABLED = "editor_folding_enabled"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * narrative section/paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_NARRATIVE = "editor_folding_narrative"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * directive paragraph (%%zchar).
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_ZCHAR = "editor_folding_ZCHAR"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * ZED.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_ZED = "editor_folding_zed"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * section header paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_ZSECTION = "editor_folding_zsection"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * axiomatic description paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_AX = "editor_folding_ax"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * schema definition paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_SCH = "editor_folding_sch"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * generic axiomatic description paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_GENAX = "editor_folding_genax"; //$NON-NLS-1$
  
  /**
   * A named preference that controls whether the editor folds the element - 
   * generic schema definition paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_FOLDING_GENSCH = "editor_folding_gensch"; //$NON-NLS-1$
  
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
  public static final String INSERT_ZCHAR = "charmapview.InsertZChar"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>SINGLE_CLICK</code>.
   * 
   * @see #CLICK
   */
  public static final String INSERT_ZCHAR_BY_CLICK = "charmapview.SingleClick"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>DOUBLE_CLICK</code>.
   * 
   * @see #DOUBLE_CLICK
   */
  public static final String INSERT_ZCHAR_BY_DOUBLE_CLICK = "charmapview.DoubleClick"; //$NON-NLS-1$

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
    store.setDefault(
        PreferenceConstants.PROP_EXTRACT_COMMA_OR_SEMI_FROM_DECORWORDS, true);

    store.setDefault(PreferenceConstants.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS,
        true);

    store.setDefault(PreferenceConstants.PROP_TYPECHECK_USE_BEFORE_DECL, true);

    store
        .setDefault(PreferenceConstants.PROP_TYPECHECK_USE_STRONG_TYPING, true);

    // Editor base preference page
    store.setDefault(PreferenceConstants.EDITOR_PARSING_ENABLED, true);
    store.setDefault(PreferenceConstants.EDITOR_REPORT_PROBLEMS,
        PreferenceConstants.EDITOR_REPORT_PROBLEMS_WHILE_EDITING);
    store.setDefault(PreferenceConstants.EDITOR_MATCHING_BRACKETS, true);
    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_MATCHING_BRACKETS_COLOR, new RGB(192, 192,
            192));
    store.setDefault(PreferenceConstants.EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE,
        true);
    store.setDefault(PreferenceConstants.EDITOR_SHOW_HOVER, true);
//    store.setDefault(PreferenceConstants.EDITOR_ANNOTATION_ROLL_OVER, true);
    store.setDefault(PreferenceConstants.EDITOR_MARK_OCCURRENCES, true);
//    store.setDefault(PreferenceConstants.EDITOR_STICKY_OCCURRENCES, true);
    store.setDefault(
        PreferenceConstants.EDITOR_MARK_OCCURRENCES_WHEN_HIGHLIGHTING_TERM,
        true);
    
    // Editor annotation preference page
    store.setDefault(EDITOR_ANNOTATION_SCHEMABOX_ENABLE, true);
    store.setDefault(EDITOR_ANNOTATION_SCHEMABOX_STYLE, PreferenceConstants.EDITOR_ANNOTATION_SCHEMABOX_STYLE_2);
    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_ANNOTATION_SCHEMABOX_LINE_COLOR, new RGB(255, 100, 100));
    store.setDefault(EDITOR_ANNOTATION_SCHEMABOX_LINE_WIDTH, 1);


    //  Folding preference page
    store.setDefault(PreferenceConstants.EDITOR_FOLDING_ENABLED, true);
    store.setDefault(PreferenceConstants.EDITOR_FOLDING_NARRATIVE, true);
    store.setDefault(PreferenceConstants.EDITOR_FOLDING_ZCHAR, true);
    store.setDefault(PreferenceConstants.EDITOR_FOLDING_ZED, true);
    store.setDefault(PreferenceConstants.EDITOR_FOLDING_ZSECTION, true);
    store.setDefault(PreferenceConstants.EDITOR_FOLDING_AX, true);
    store.setDefault(PreferenceConstants.EDITOR_FOLDING_SCH, true);
    store.setDefault(PreferenceConstants.EDITOR_FOLDING_GENAX, true);
    store.setDefault(PreferenceConstants.EDITOR_FOLDING_GENSCH, true);
    
    // Syntax coloring preference page
    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_Z_NARRATIVE_FOREGROUND, new RGB(128, 0, 0));
    store.setDefault(PreferenceConstants.EDITOR_Z_NARRATIVE_BOLD, false);
    store.setDefault(PreferenceConstants.EDITOR_Z_NARRATIVE_ITALIC, false);

    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_Z_COMMENT_FOREGROUND, new RGB(128, 128, 0));
    store.setDefault(PreferenceConstants.EDITOR_Z_COMMENT_BOLD, false);
    store.setDefault(PreferenceConstants.EDITOR_Z_COMMENT_ITALIC, false);

    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_Z_KEYWORD_FOREGROUND, new RGB(64, 64, 128));
    store.setDefault(PreferenceConstants.EDITOR_Z_KEYWORD_BOLD, true);
    store.setDefault(PreferenceConstants.EDITOR_Z_KEYWORD_ITALIC, false);

    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_Z_OPERATOR_FOREGROUND, new RGB(64, 64, 128));
    store.setDefault(PreferenceConstants.EDITOR_Z_OPERATOR_BOLD, true);
    store.setDefault(PreferenceConstants.EDITOR_Z_OPERATOR_ITALIC, false);

    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_Z_DEFAULT_FOREGROUND, new RGB(0, 0, 0));
    store.setDefault(PreferenceConstants.EDITOR_Z_DEFAULT_BOLD, false);
    store.setDefault(PreferenceConstants.EDITOR_Z_DEFAULT_ITALIC, false);

    //  semantic highlighting
    //    SemanticHighlightings.initDefaults(store);

    // do more complicated stuff
    //		NewJavaProjectPreferencePage.initDefaults(store);

    // work in progress
    //		WorkInProgressPreferencePage.initDefaults(store);

    // reset preferences that are not settable by fEditor any longer
    // see AbstractDecoratedTextEditorPreferenceConstants
    //		store.setToDefault(EDITOR_LINE_NUMBER_RULER); // global
    //		store.setToDefault(EDITOR_LINE_NUMBER_RULER_COLOR); // global
    //		store.setToDefault(EDITOR_OVERVIEW_RULER); // removed -> true
    //		store.setToDefault(AbstractDecoratedTextEditorPreferenceConstants.EDITOR_USE_CUSTOM_CARETS); // accessibility

    //		store.setToDefault(PreferenceConstants.EDITOR_CURRENT_LINE); // global
    //		store.setToDefault(PreferenceConstants.EDITOR_CURRENT_LINE_COLOR); // global

    //		store.setToDefault(PreferenceConstants.EDITOR_PRINT_MARGIN); // global
    //		store.setToDefault(PreferenceConstants.EDITOR_PRINT_MARGIN_COLUMN); // global
    //		store.setToDefault(PreferenceConstants.EDITOR_PRINT_MARGIN_COLOR); // global

    //		store.setToDefault(PreferenceConstants.EDITOR_FOREGROUND_COLOR); // global
    //		store.setToDefault(PreferenceConstants.EDITOR_FOREGROUND_DEFAULT_COLOR); // global
    //		store.setToDefault(PreferenceConstants.EDITOR_BACKGROUND_COLOR); // global
    //		store.setToDefault(PreferenceConstants.EDITOR_BACKGROUND_DEFAULT_COLOR); // global
    //		store.setToDefault(AbstractDecoratedTextEditorPreferenceConstants.EDITOR_SELECTION_FOREGROUND_DEFAULT_COLOR); // global
    //		store.setToDefault(AbstractDecoratedTextEditorPreferenceConstants.EDITOR_SELECTION_BACKGROUND_DEFAULT_COLOR); // global

    //		store.setToDefault(PreferenceConstants.EDITOR_DISABLE_OVERWRITE_MODE); // global

    //		store.setToDefault(PreferenceConstants.EDITOR_SEMANTIC_HIGHLIGHTING_ENABLED); // removed
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

  /**
   * Returns the value for the given key in the given context.
   * @param key The preference key
   * @param project The current context or <code>null</code> if no context is available and the
   * workspace setting should be taken. Note that passing <code>null</code> should
   * be avoided.
   * @return Returns the current value for the string.
   * @since 3.1
   */
  /*	public static String getPreference(String key, IJavaProject project) {
   String val;
   if (project != null) {
   val= new ProjectScope(project.getProject()).getNode(JavaUI.ID_PLUGIN).get(key, null);
   if (val != null) {
   return val;
   }
   }
   val= new InstanceScope().getNode(JavaUI.ID_PLUGIN).get(key, null);
   if (val != null) {
   return val;
   }
   return new DefaultScope().getNode(JavaUI.ID_PLUGIN).get(key, null);
   }
   */
}
