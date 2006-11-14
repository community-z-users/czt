/**
 * 
 */

package net.sourceforge.czt.eclipse.preferences;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.util.IZColorConstants;

import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.preferences.DefaultScope;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.ui.texteditor.AbstractTextEditor;

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
   * Syntax coloring preference keys
   */

  /**
   * Preference key suffix for foreground text color preference keys
   */
  public static final String EDITOR_FOREGROUND_SUFFIX = "_foreground";

  /**
   * Preference key suffix for bold text style preference keys.
   * 
   * @since 2.1
   */
  public static final String EDITOR_BOLD_SUFFIX = "_bold"; //$NON-NLS-1$

  /**
   * Preference key suffix for italic text style preference keys.
   * 
   * @since 3.0
   */
  public static final String EDITOR_ITALIC_SUFFIX = "_italic"; //$NON-NLS-1$

  /**
   * Preference key suffix for strikethrough text style preference keys.
   * 
   * @since 3.1
   */
  public static final String EDITOR_STRIKETHROUGH_SUFFIX = "_strikethrough"; //$NON-NLS-1$

  /**
   * Preference key suffix for underline text style preference keys.
   * 
   * @since 3.1
   */
  public static final String EDITOR_UNDERLINE_SUFFIX = "_underline"; //$NON-NLS-1$

  /**
   * The symbolic font name for the Java fEditor text font 
   * (value <code>"org.eclipse.jdt.ui.editors.textfont"</code>).
   * 
   * @since 2.1
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
  public final static String EDITOR_Z_NARRATIVE_FOREGROUND = IZColorConstants.CZT_NARRATIVE + EDITOR_FOREGROUND_SUFFIX;

  /**
   * A named preference that controls whether narrative paragraphs are rendered in bold.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in bold. If <code>false</code> the are rendered using no font style attribute.
   * </p>
   */
  public final static String EDITOR_Z_NARRATIVE_BOLD = IZColorConstants.CZT_NARRATIVE + EDITOR_BOLD_SUFFIX;

  /**
   * A named preference that controls whether narrative paragraphs are rendered in italic.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in italic. If <code>false</code> the are rendered using no italic font style attribute.
   * </p>
   * 
   * @since 3.0
   */
  public final static String EDITOR_Z_NARRATIVE_ITALIC = IZColorConstants.CZT_NARRATIVE + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether narrative paragraphs are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in strikethrough. If <code>false</code> the are rendered using no strikethrough font style attribute.
   * </p>
   * 
   * @since 3.1
   */
  public final static String EDITOR_Z_NARRATIVE_STRIKETHROUGH = IZColorConstants.CZT_NARRATIVE + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether narrative paragraphs are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in underline. If <code>false</code> the are rendered using no underline font style attribute.
   * </p>
   * 
   * @since 3.1
   */
  public final static String EDITOR_Z_NARRATIVE_UNDERLINE = IZColorConstants.CZT_NARRATIVE + EDITOR_UNDERLINE_SUFFIX;

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
   * 
   * @since 3.0
   */
  public final static String EDITOR_Z_COMMENT_ITALIC = IZColorConstants.CZT_COMMENT
      + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether single-line comments are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in strikethrough. If <code>false</code> the are rendered using no strikethrough font style attribute.
   * </p>
   * 
   * @since 3.1
   */
  public final static String EDITOR_Z_COMMENT_STRIKETHROUGH = IZColorConstants.CZT_COMMENT
      + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether single-line comments are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true</code> multi-line comments are rendered
   * in underline. If <code>false</code> the are rendered using no underline font style attribute.
   * </p>
   * 
   * @since 3.1
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
   * 
   * @since 3.0
   */
  public final static String EDITOR_Z_KEYWORD_ITALIC = IZColorConstants.CZT_KEYWORD
      + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether keywords are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   * 
   * @since 3.1
   */
  public final static String EDITOR_Z_KEYWORD_STRIKETHROUGH = IZColorConstants.CZT_KEYWORD
      + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether keywords are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   * 
   * @since 3.1
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
   * 
   * @since 3.0
   */
  public final static String EDITOR_Z_OPERATOR_ITALIC = IZColorConstants.CZT_OPERATOR
      + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether operators are rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   * 
   * @since 3.1
   */
  public final static String EDITOR_Z_OPERATOR_STRIKETHROUGH = IZColorConstants.CZT_OPERATOR
      + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether operators are rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   * 
   * @since 3.1
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
   * 
   * @since 3.0
   */
  public final static String EDITOR_Z_DEFAULT_ITALIC = IZColorConstants.CZT_DEFAULT
      + EDITOR_ITALIC_SUFFIX;

  /**
   * A named preference that controls whether Z default text is rendered in strikethrough.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   * 
   * @since 3.1
   */
  public final static String EDITOR_Z_DEFAULT_STRIKETHROUGH = IZColorConstants.CZT_DEFAULT
      + EDITOR_STRIKETHROUGH_SUFFIX;

  /**
   * A named preference that controls whether Z default text is rendered in underline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   * 
   * @since 3.1
   */
  public final static String EDITOR_Z_DEFAULT_UNDERLINE = IZColorConstants.CZT_DEFAULT
      + EDITOR_UNDERLINE_SUFFIX;

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
   * A named preference that controls whether Z outline view update its presentation while editing or when saving the
   * content of an fEditor. 
   * <p>
   * Value is of type <code>String</code>: possible values are <code>
   * UPDATE_ON_SAVE</code> or <code>
   * UPDATE_WHILE_EDITING</code>.
   * </p>
   * 
   * @see #UPDATE_OUTLINE_ON_SAVE
   * @see #UPDATE_OUTLINE_WHILE_EDITING
   */
  public static final String UPDATE_Z_OUTLINE_VIEW = "outlineview.Update"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>UPDATE_Z_VIEWS</code>
   * 
   * @see #UPDATE_Z_OUTLINE_VIEW
   */
  public static final String UPDATE_OUTLINE_ON_SAVE = "outlineview.update.OnSave"; //$NON-NLS-1$

  /**
   * A string value used by the named preference <code>UPDATE_Z_VIEWS</code>
   * 
   * @see #UPDATE_Z_OUTLINE_VIEW
   */
  public static final String UPDATE_OUTLINE_WHILE_EDITING = "outlineview.update.WhileEditing"; //$NON-NLS-1$

  /**
   * A named preference that controls whether the outline view selection
   * should stay in sync with with the element at the current cursor position.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   * @since 2.1
   */
  public final static String EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE = "ZEditor.SyncOutlineOnCursorMove"; //$NON-NLS-1$

  /**
   * A named preference that controls whether hover tool tips in the fEditor are turned on or off.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String EDITOR_SHOW_HOVER = "org.eclipse.jdt.ui.editor.showHover"; //$NON-NLS-1$

  /**
   * A named preference that controls whether occurrences are marked in the fEditor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   *
   * @since 3.0
   */
  public static final String EDITOR_MARK_OCCURRENCES = "MarkOccurrences"; //$NON-NLS-1$

  /**
   * A named preference that controls whether occurrences are marked in the fEditor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   *
   * @since 3.0
   */
  public static final String EDITOR_MARK_OCCURRENCES_WHEN_EXPANSION = "MarkOccurrencesWhenExpansion"; //$NON-NLS-1$

  /**
   * A named preference that controls whether occurrences are sticky in the fEditor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   *
   * @since 3.0
   */
  public static final String EDITOR_STICKY_OCCURRENCES = "StickyOccurrences"; //$NON-NLS-1$

  /**
   * A named preference that controls whether annotation roll over is used or not.
   * <p>
   * Value is of type <code>Boolean</code>. If <code>true<code> the annotation ruler column
   * uses a roll over to display multiple annotations
   * </p>
   * 
   * @since 3.0
   */
  public static final String EDITOR_ANNOTATION_ROLL_OVER = "editor_annotation_roll_over"; //$NON-NLS-1$

  /**
   * A named preference that controls whether folding is enabled in the Z fEditor.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   * 
   * @since 3.0
   */
  public static final String EDITOR_FOLDING_ENABLED = "editor_folding_enabled"; //$NON-NLS-1$

  /**
   * Initializes the given preference store with the default values.
   * 
   * @param store the preference store to be initialized
   * 
   * @since 2.1
   */
  public static void initializeDefaultValues(IPreferenceStore store)
  {

    // ZBasePreferencePage
    //		store.setDefault(PreferenceConstants.DOUBLE_CLICK, PreferenceConstants.DOUBLE_CLICK_EXPANDS);
    //		store.setDefault(PreferenceConstants.UPDATE_Z_VIEWS, PreferenceConstants.UPDATE_WHILE_EDITING);	
    //		store.setToDefault(PreferenceConstants.UPDATE_Z_VIEWS); // clear preference, update on save not supported anymore

    //		store.setDefault(PreferenceConstants.SEARCH_USE_REDUCED_MENU, true);
    // AppearancePreferencePage
    //		store.setDefault(PreferenceConstants.APPEARANCE_PKG_NAME_PATTERN_FOR_PKG_VIEW, ""); //$NON-NLS-1$
    //		store.setDefault(PreferenceConstants.APPEARANCE_FOLD_PACKAGES_IN_PACKAGE_EXPLORER, true);

    // CompilerPreferencePage
    // no initialization needed

    // RefactoringPreferencePage
    //		store.setDefault(PreferenceConstants.REFACTOR_SAVE_ALL_EDITORS, false);		

    // TemplatePreferencePage
    //		store.setDefault(PreferenceConstants.TEMPLATES_USE_CODEFORMATTER, true);

    // CodeGenerationPreferencePage
    // compatibility code

    // ZEditorPreferencePage
    store.setDefault(PreferenceConstants.EDITOR_MATCHING_BRACKETS, true);
    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_MATCHING_BRACKETS_COLOR, new RGB(192, 192,
            192));

    //		PreferenceConverter.setDefault(store, PreferenceConstants.EDITOR_FIND_SCOPE_COLOR, new RGB(185, 176 , 180));

    //		store.setDefault(PreferenceConstants.EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE, true);

    //		PreferenceConverter.setDefault(store, PreferenceConstants.EDITOR_LINKED_POSITION_COLOR, new RGB(121, 121, 121));

    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_Z_NARRATIVE_FOREGROUND,
        new RGB(128, 0, 0));
    store.setDefault(PreferenceConstants.EDITOR_Z_NARRATIVE_BOLD, false);
    store.setDefault(PreferenceConstants.EDITOR_Z_NARRATIVE_ITALIC, false);

    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_Z_COMMENT_FOREGROUND, new RGB(128,
            128, 0));
    store
        .setDefault(PreferenceConstants.EDITOR_Z_COMMENT_BOLD, false);
    store.setDefault(PreferenceConstants.EDITOR_Z_COMMENT_ITALIC,
        false);

    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_Z_KEYWORD_FOREGROUND, new RGB(64, 64, 128));
    store.setDefault(PreferenceConstants.EDITOR_Z_KEYWORD_BOLD, true);
    store.setDefault(PreferenceConstants.EDITOR_Z_KEYWORD_ITALIC, false);

    PreferenceConverter.setDefault(store,
        PreferenceConstants.EDITOR_Z_OPERATOR_FOREGROUND, new RGB(64, 64, 128));
    store.setDefault(PreferenceConstants.EDITOR_Z_OPERATOR_BOLD, true);
    store.setDefault(PreferenceConstants.EDITOR_Z_OPERATOR_ITALIC, false);

    PreferenceConverter
        .setDefault(store, PreferenceConstants.EDITOR_Z_DEFAULT_FOREGROUND,
            new RGB(0, 0, 0));
    store.setDefault(PreferenceConstants.EDITOR_Z_DEFAULT_BOLD, false);
    store.setDefault(PreferenceConstants.EDITOR_Z_DEFAULT_ITALIC, false);

    // mark occurrences
    //		store.setDefault(PreferenceConstants.EDITOR_MARK_OCCURRENCES, true);
    //		store.setDefault(PreferenceConstants.EDITOR_STICKY_OCCURRENCES, true);

    // folding
    //		store.setDefault(PreferenceConstants.EDITOR_FOLDING_ENABLED, true);
    //		store.setDefault(PreferenceConstants.EDITOR_FOLDING_PROVIDER, "org.eclipse.jdt.ui.text.defaultFoldingProvider"); //$NON-NLS-1$
    //		store.setDefault(PreferenceConstants.EDITOR_FOLDING_METHODS, false);

    // semantic highlighting
    //		SemanticHighlightings.initDefaults(store);

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
