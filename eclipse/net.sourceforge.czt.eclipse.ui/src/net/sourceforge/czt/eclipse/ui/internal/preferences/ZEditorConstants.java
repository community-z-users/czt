package net.sourceforge.czt.eclipse.ui.internal.preferences;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.RGB;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.internal.util.IZColorConstants;

public class ZEditorConstants
{

  private static final String EDITOR_PREF = CztUIPlugin.PLUGIN_ID + ".editor";
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
  public static final String PARSING_ENABLED = EDITOR_PREF + ".parsing_enabled"; //$NON-NLS-1$
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
   * @see #REPORT_PROBLEMS_ON_SAVE
   * @see #REPORT_PROBLEMS_WHILE_EDITING
   */
  public static final String REPORT_PROBLEMS = EDITOR_PREF + ".report.problems"; //$NON-NLS-1$
  /**
   * A string value used by the named preference <code>REPORT_PROBLEMS</code>
   * 
   * @see #REPORT_PROBLEMS
   */
  public static final String REPORT_PROBLEMS_ON_SAVE = EDITOR_PREF + ".report.problems.OnSave"; //$NON-NLS-1$
  /**
   * A string value used by the named preference <code>REPORT_PROBLEMS</code>
   * 
   * @see #REPORT_PROBLEMS
   */
  public static final String REPORT_PROBLEMS_WHILE_EDITING = EDITOR_PREF + ".report.problems.WhileEditing"; //$NON-NLS-1$
  /**
   * A named preference that controls whether bracket matching highlighting is turned on or off.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String MATCHING_BRACKETS = EDITOR_PREF + ".MatchingBrackets"; //$NON-NLS-1$
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
  public final static String MATCHING_BRACKETS_COLOR = EDITOR_PREF + ".MatchingBracketsColor"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the outline view selection
   * should stay in sync with with element at the current cursor position.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String SYNC_OUTLINE_ON_CURSOR_MOVE = EDITOR_PREF + ".SyncOutlineOnCursorMove"; //$NON-NLS-1$
  /*
   * Hover preference keys
   */
  /**
   * A named preference that controls whether hover tool tips in the Z editor are turned on or off.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String SHOW_HOVER = EDITOR_PREF + ".showHover"; //$NON-NLS-1$
  /**
   * A named preference that controls whether annotation roll over is used or not.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true<code> the annotation ruler column
   * uses a roll over to display multiple annotations
   * </p>
   */
  public static final String ANNOTATION_ROLL_OVER = ANNOTATION_PREF + ".rollover"; //$NON-NLS-1$
  /*
   * Mark occurrence preference keys
   */
  /**
   * A named preference that controls whether occurrences are marked in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String MARK_OCCURRENCES = EDITOR_PREF + ".MarkOccurrences"; //$NON-NLS-1$
  /**
   * A named preference that controls whether occurrences are sticky in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String STICKY_OCCURRENCES = EDITOR_PREF + ".StickyOccurrences"; //$NON-NLS-1$
  /*
   * Annotation preference keys
   */
  /**
   * A named preference that controls whether the editor draws schema boxes.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String ANNOTATION_SCHEMABOX_ENABLE = ANNOTATION_PREF + ".schemabox.enable";
  /**
   * A named preference that controls the style that the editor uses to draw the schema boxes. 
   * <p>
   * Value is of type <code>String</code>: possible values are <code>
   * ANNOTATION_SCHEMABOX_STYLE_1</code> or <code>
   * ANNOTATION_SCHEMABOX_STYLE_2</code>.
   * </p>
   * 
   * @see #ANNOTATION_SCHEMABOX_STYLE_1
   * @see #ANNOTATION_SCHEMABOX_STYLE_2
   */
  public final static String ANNOTATION_SCHEMABOX_STYLE = ANNOTATION_PREF + ".schemabox.style";
  /**
   * A string value used by the named preference <code>ANNOTATION_SCHEMABOX_STYLE</code>
   * 
   * @see #ANNOTATION_SCHEMABOX_STYLE
   */
  public final static String ANNOTATION_SCHEMABOX_STYLE_1 = ANNOTATION_PREF + ".schemabox.style_1";
  /**
   * A string value used by the named preference <code>ANNOTATION_SCHEMABOX_STYLE</code>
   * 
   * @see #ANNOTATION_SCHEMABOX_STYLE
   */
  public final static String ANNOTATION_SCHEMABOX_STYLE_2 = ANNOTATION_PREF + ".schemabox.style_2";
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
  public final static String ANNOTATION_SCHEMABOX_LINE_COLOR = ANNOTATION_PREF + ".schemabox.line_color";
  /**
   * A named preference that holds the width used to draw schema boxes.
   * <p>
   * Value is of type <code>int</code>.
   * </p>
   */
  public final static String ANNOTATION_SCHEMABOX_LINE_WIDTH = ANNOTATION_PREF + ".schemabox.line_width";
  /*
   * Folding preference keys
   */
  /**
   * A named preference that controls whether folding is enabled in the CZT editor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_ENABLED = EDITOR_PREF + ".folding.enabled"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds the element - 
   * narrative section/paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_NARRATIVE = EDITOR_PREF + ".folding_narrative"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds the element - 
   * directive paragraph (%%zchar).
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_ZCHAR = EDITOR_PREF + ".folding_ZCHAR"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds the element - 
   * ZED.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_ZED = EDITOR_PREF + ".folding_zed"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds the element - 
   * section header paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_ZSECTION = EDITOR_PREF + ".folding_zsection"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds the element - 
   * axiomatic description paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_AX = EDITOR_PREF + ".folding_ax"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds the element - 
   * schema definition paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_SCH = EDITOR_PREF + ".folding_sch"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds the element - 
   * generic axiomatic description paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_GENAX = EDITOR_PREF + ".folding_genax"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds the element - 
   * generic schema definition paragraph.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_GENSCH = EDITOR_PREF + ".folding_gensch"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds theorem paragraphs.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_THEOREM = EDITOR_PREF + ".folding_theorem"; //$NON-NLS-1$
  /**
   * A named preference that controls whether the editor folds proof script paragraphs.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String FOLDING_PROOFSCRIPT = EDITOR_PREF + ".folding_proofscript"; //$NON-NLS-1$
  
  /*
   * Syntax coloring preference keys
   */
  /**
   * Preference key suffix for foreground text color preference keys
   */
  public static final String SUFFIX_FOREGROUND = "_foreground";
  /**
   * Preference key suffix for bold text style preference keys.
   */
  public static final String SUFFIX_BOLD = "_bold"; //$NON-NLS-1$
  /**
   * Preference key suffix for italic text style preference keys.
   */
  public static final String SUFFIX_ITALIC = "_italic"; //$NON-NLS-1$
  /**
   * Preference key suffix for strikethrough text style preference keys.
   */
  public static final String SUFFIX_STRIKETHROUGH = "_strikethrough"; //$NON-NLS-1$
  /**
   * Preference key suffix for underline text style preference keys.
   */
  public static final String SUFFIX_UNDERLINE = "_underline"; //$NON-NLS-1$
  
  /*
   * Font preference keys
   */
  /**
   * The symbolic font name for Z Editor font when editing Unicode specifications
   */
  public final static String FONT_UNICODE = EDITOR_PREF + ".font.unicode"; //$NON-NLS-1$
  /**
   * The symbolic font name for Z Editor font when editing LaTeX specifications
   */
  public final static String FONT_LATEX = EDITOR_PREF + ".font.latex"; //$NON-NLS-1$
  
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
  public final static String Z_NARRATIVE_FOREGROUND = IZColorConstants.CZT_NARRATIVE
      + SUFFIX_FOREGROUND;
  /**
   * A named preference that controls whether narrative paragraphs are rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in bold. If <code>false</code> the are rendered using no font style attribute.
   * </p>
   */
  public final static String Z_NARRATIVE_BOLD = IZColorConstants.CZT_NARRATIVE
      + SUFFIX_BOLD;
  /**
   * A named preference that controls whether narrative paragraphs are rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in italic. If <code>false</code> the are rendered using no italic font style attribute.
   * </p>
   */
  public final static String Z_NARRATIVE_ITALIC = IZColorConstants.CZT_NARRATIVE
      + SUFFIX_ITALIC;
  /**
   * A named preference that controls whether narrative paragraphs are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in strikethrough. If <code>false</code> the are rendered using no strikethrough font style attribute.
   * </p>
   */
  public final static String Z_NARRATIVE_STRIKETHROUGH = IZColorConstants.CZT_NARRATIVE
      + SUFFIX_STRIKETHROUGH;
  /**
   * A named preference that controls whether narrative paragraphs are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in underline. If <code>false</code> the are rendered using no underline font style attribute.
   * </p>
   */
  public final static String Z_NARRATIVE_UNDERLINE = IZColorConstants.CZT_NARRATIVE
      + SUFFIX_UNDERLINE;
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
  public final static String Z_COMMENT_FOREGROUND = IZColorConstants.CZT_COMMENT
      + SUFFIX_FOREGROUND;
  /**
   * A named preference that controls whether single-line comments are rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in bold. If <code>false</code> the are rendered using no font style attribute.
   * </p>
   */
  public final static String Z_COMMENT_BOLD = IZColorConstants.CZT_COMMENT
      + SUFFIX_BOLD;
  /**
   * A named preference that controls whether single-line comments are rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in italic. If <code>false</code> the are rendered using no italic font style attribute.
   * </p>
   */
  public final static String Z_COMMENT_ITALIC = IZColorConstants.CZT_COMMENT
      + SUFFIX_ITALIC;
  /**
   * A named preference that controls whether single-line comments are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in strikethrough. If <code>false</code> the are rendered using no strikethrough font style attribute.
   * </p>
   */
  public final static String Z_COMMENT_STRIKETHROUGH = IZColorConstants.CZT_COMMENT
      + SUFFIX_STRIKETHROUGH;
  /**
   * A named preference that controls whether single-line comments are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in underline. If <code>false</code> the are rendered using no underline font style attribute.
   * </p>
   */
  public final static String Z_COMMENT_UNDERLINE = IZColorConstants.CZT_COMMENT
      + SUFFIX_UNDERLINE;
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
  public final static String Z_KEYWORD_FOREGROUND = IZColorConstants.CZT_KEYWORD
      + SUFFIX_FOREGROUND;
  /**
   * A named preference that controls whether keywords are rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_KEYWORD_BOLD = IZColorConstants.CZT_KEYWORD
      + SUFFIX_BOLD;
  /**
   * A named preference that controls whether keywords are rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_KEYWORD_ITALIC = IZColorConstants.CZT_KEYWORD
      + SUFFIX_ITALIC;
  /**
   * A named preference that controls whether keywords are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_KEYWORD_STRIKETHROUGH = IZColorConstants.CZT_KEYWORD
      + SUFFIX_STRIKETHROUGH;
  /**
   * A named preference that controls whether keywords are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_KEYWORD_UNDERLINE = IZColorConstants.CZT_KEYWORD
      + SUFFIX_UNDERLINE;
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
  public final static String Z_OPERATOR_FOREGROUND = IZColorConstants.CZT_OPERATOR
      + SUFFIX_FOREGROUND;
  /**
   * A named preference that controls whether operators are rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_OPERATOR_BOLD = IZColorConstants.CZT_OPERATOR
      + SUFFIX_BOLD;
  /**
   * A named preference that controls whether operators are rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_OPERATOR_ITALIC = IZColorConstants.CZT_OPERATOR
      + SUFFIX_ITALIC;
  /**
   * A named preference that controls whether operators are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_OPERATOR_STRIKETHROUGH = IZColorConstants.CZT_OPERATOR
      + SUFFIX_STRIKETHROUGH;
  /**
   * A named preference that controls whether operators are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_OPERATOR_UNDERLINE = IZColorConstants.CZT_OPERATOR
      + SUFFIX_UNDERLINE;
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
  public final static String Z_DEFAULT_FOREGROUND = IZColorConstants.CZT_DEFAULT
      + SUFFIX_FOREGROUND;
  /**
   * A named preference that controls whether Z default text is rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_DEFAULT_BOLD = IZColorConstants.CZT_DEFAULT
      + SUFFIX_BOLD;
  /**
   * A named preference that controls whether Z default text is rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_DEFAULT_ITALIC = IZColorConstants.CZT_DEFAULT
      + SUFFIX_ITALIC;
  /**
   * A named preference that controls whether Z default text is rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_DEFAULT_STRIKETHROUGH = IZColorConstants.CZT_DEFAULT
      + SUFFIX_STRIKETHROUGH;
  /**
   * A named preference that controls whether Z default text is rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public final static String Z_DEFAULT_UNDERLINE = IZColorConstants.CZT_DEFAULT
      + SUFFIX_UNDERLINE;

  private ZEditorConstants() {}
  
  /**
   * Initializes the given preference store with the default values.
   * 
   * @param store the preference store to be initialized
   */
  public static void initializeDefaultValues(IPreferenceStore store)
  {

    // Editor base preference page
    store.setDefault(PARSING_ENABLED, true);
    store.setDefault(REPORT_PROBLEMS, REPORT_PROBLEMS_WHILE_EDITING);
    store.setDefault(MATCHING_BRACKETS, true);
    PreferenceConverter.setDefault(store, MATCHING_BRACKETS_COLOR, new RGB(192, 192, 192));
    store.setDefault(SYNC_OUTLINE_ON_CURSOR_MOVE, true);
    store.setDefault(SHOW_HOVER, true);
//    store.setDefault(ANNOTATION_ROLL_OVER, true);
    store.setDefault(MARK_OCCURRENCES, true);
//    store.setDefault(STICKY_OCCURRENCES, true);
    
    // Editor annotation preference page
    store.setDefault(ANNOTATION_SCHEMABOX_ENABLE, true);
    store.setDefault(ANNOTATION_SCHEMABOX_STYLE, ANNOTATION_SCHEMABOX_STYLE_2);
    PreferenceConverter.setDefault(store, ANNOTATION_SCHEMABOX_LINE_COLOR, new RGB(255, 100, 100));
    store.setDefault(ANNOTATION_SCHEMABOX_LINE_WIDTH, 0);


    //  Folding preference page
    store.setDefault(FOLDING_ENABLED, true);
    store.setDefault(FOLDING_NARRATIVE, true);
    store.setDefault(FOLDING_ZCHAR, true);
    store.setDefault(FOLDING_ZED, true);
    store.setDefault(FOLDING_ZSECTION, true);
    store.setDefault(FOLDING_AX, true);
    store.setDefault(FOLDING_SCH, true);
    store.setDefault(FOLDING_GENAX, true);
    store.setDefault(FOLDING_GENSCH, true);
    store.setDefault(FOLDING_THEOREM, true);
    store.setDefault(FOLDING_PROOFSCRIPT, true);
    
    // Syntax coloring preference page
    PreferenceConverter.setDefault(store, Z_NARRATIVE_FOREGROUND, new RGB(128, 0, 0));
    store.setDefault(Z_NARRATIVE_BOLD, false);
    store.setDefault(Z_NARRATIVE_ITALIC, false);

    PreferenceConverter.setDefault(store, Z_COMMENT_FOREGROUND, new RGB(128, 128, 0));
    store.setDefault(Z_COMMENT_BOLD, false);
    store.setDefault(Z_COMMENT_ITALIC, false);

    PreferenceConverter.setDefault(store, Z_KEYWORD_FOREGROUND, new RGB(64, 64, 128));
    store.setDefault(Z_KEYWORD_BOLD, true);
    store.setDefault(Z_KEYWORD_ITALIC, false);

    PreferenceConverter.setDefault(store, Z_OPERATOR_FOREGROUND, new RGB(64, 64, 128));
    store.setDefault(Z_OPERATOR_BOLD, true);
    store.setDefault(Z_OPERATOR_ITALIC, false);

    PreferenceConverter.setDefault(store, Z_DEFAULT_FOREGROUND, new RGB(0, 0, 0));
    store.setDefault(Z_DEFAULT_BOLD, false);
    store.setDefault(Z_DEFAULT_ITALIC, false);
  }
  
}
