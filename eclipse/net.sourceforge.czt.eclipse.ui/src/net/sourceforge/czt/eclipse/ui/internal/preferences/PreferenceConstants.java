package net.sourceforge.czt.eclipse.ui.internal.preferences;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.parser.util.ParsePropertiesKeys;
import net.sourceforge.czt.session.SectionManager;
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
   * Value can be any of Dialect enum/class.
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

  
  /**
   * A named preference that controls whether the complete syntax tree is displayed in the
   * editor outline.
   * <p>
   * Value is of type <code>Boolean</code>.
   * </p>
   */
  public static final String OUTLINE_Z_COMPLETE_TREE = CztUIPlugin.PLUGIN_ID + ".outline.completeTree"; //$NON-NLS-1$
  
  /**
   * Initializes the given preference store with the default values.
   * 
   * @param store the preference store to be initialized
   */
  public static void initializeDefaultValues(IPreferenceStore store)
  {
	  
    // Compiler preference page
    store.setDefault(PROP_DIALECT, SectionManager.DEFAULT_EXTENSION.toString());
    
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
