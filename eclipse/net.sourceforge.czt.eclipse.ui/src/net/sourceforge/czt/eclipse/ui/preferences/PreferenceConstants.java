package net.sourceforge.czt.eclipse.ui.preferences;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.parser.util.ParsePropertiesKeys;
import net.sourceforge.czt.typecheck.z.TypecheckPropertiesKeys;

import org.eclipse.jface.preference.IPreferenceStore;

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
    
    store.setDefault(OUTLINE_Z_COMPLETE_TREE, false);

    ZEditorConstants.initializeDefaultValues(store);
  }

  /**
   * Returns the CZT preference store.
   * 
   * @return the CZT preference store
   */
  public static IPreferenceStore getPreferenceStore()
  {
    return CztUIPlugin.getDefault().getPreferenceStore();
  }

}
