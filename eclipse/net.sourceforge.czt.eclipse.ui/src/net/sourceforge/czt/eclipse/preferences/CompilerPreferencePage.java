/**
 *
 */

package net.sourceforge.czt.eclipse.preferences;

import java.util.ArrayList;

import net.sourceforge.czt.eclipse.CZTPlugin;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * @author Chengdong Xu
 */
public class CompilerPreferencePage extends PreferencePage
    implements
      IWorkbenchPreferencePage
{
  private ArrayList<Button> fCheckBoxes;

  /** Combo box to select Z dialect */
  private Combo fDialectCombo;

  public CompilerPreferencePage()
  {
    super();
    setPreferenceStore(CZTPlugin.getDefault().getPreferenceStore());
    setDescription(PreferencesMessages.CompilerPreferencePage_description);
    fCheckBoxes = new ArrayList<Button>();
  }

  /*
   * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
   */
  public void init(IWorkbench workbench)
  {
  }

  /*
   * @see org.eclipse.jface.preference.PreferencePage#createControl(org.eclipse.swt.widgets.Composite)
   */
  public void createControl(Composite parent)
  {
    super.createControl(parent);
    //    PlatformUI.getWorkbench().getHelpSystem().setHelp(getControl(), IJavaHelpContextIds.JAVA_BASE_PREFERENCE_PAGE);
  }

  private Button addCheckBox(Composite parent, String label, String tooltip,
      String key)
  {
    GridData gd = new GridData(GridData.HORIZONTAL_ALIGN_FILL);

    Button button = new Button(parent, SWT.CHECK);
    button.setText(label);
    button.setToolTipText(tooltip);
    button.setData(key);
    button.setLayoutData(gd);

    button.setSelection(getPreferenceStore().getBoolean(key));

    fCheckBoxes.add(button);
    return button;
  }

  /*
   * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
   */
  @Override
  protected Control createContents(Composite parent)
  {
    initializeDialogUnits(parent);

    Composite result = new Composite(parent, SWT.NONE);
    GridLayout layout = new GridLayout();
    layout.marginHeight = convertVerticalDLUsToPixels(IDialogConstants.VERTICAL_MARGIN);
    layout.marginWidth = 0;
    layout.verticalSpacing = convertVerticalDLUsToPixels(10);
    layout.horizontalSpacing = convertHorizontalDLUsToPixels(IDialogConstants.HORIZONTAL_SPACING);
    result.setLayout(layout);

    // MARKU: add a combo box to select Z dialect
    fDialectCombo = new Combo(result, SWT.NONE);
    GridData gd = new GridData(GridData.HORIZONTAL_ALIGN_BEGINNING);
    fDialectCombo.setLayoutData(gd);
    fDialectCombo.setItems(new String[]{"z", "oz", "circus", "zeves", "zpatt"});
    fDialectCombo.setToolTipText(PreferencesMessages.CompilerPreferencePage_dialect_tooltip);
    fDialectCombo.select(fDialectCombo.indexOf(
        getPreferenceStore().getString(PreferenceConstants.PROP_DIALECT)));
    
    // Add a group containing all the parsing/typechecking properties
    Group propertiesGroup = new Group(result, SWT.NONE);
    propertiesGroup.setLayout(new GridLayout());
    propertiesGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
    propertiesGroup
        .setText(PreferencesMessages.CompilerPreferencePage_properties);

    addCheckBox(
        propertiesGroup,
        PreferencesMessages.CompilerPreferencePage_ignore_unknown_latex_commands,
        PreferencesMessages.CompilerPreferencePage_ignore_unknown_latex_commands_tooltip,
        PreferenceConstants.PROP_IGNORE_UNKNOWN_LATEX_COMMANDS);
    addCheckBox(
        propertiesGroup,
        PreferencesMessages.CompilerPreferencePage_typecheck_recursive_types,
        PreferencesMessages.CompilerPreferencePage_typecheck_recursive_types_tooltip,
        PreferenceConstants.PROP_TYPECHECK_RECURSIVE_TYPES);
    addCheckBox(
        propertiesGroup,
        PreferencesMessages.CompilerPreferencePage_typecheck_use_strong_typing,
        PreferencesMessages.CompilerPreferencePage_typecheck_use_strong_typing_tooltip,
        PreferenceConstants.PROP_TYPECHECK_USE_STRONG_TYPING);

    Dialog.applyDialogFont(result);
    return result;
  }

  /*
   * @see @see org.eclipse.jface.preference.PreferencePage#performDefaults()
   */
  protected void performDefaults()
  {
    IPreferenceStore store = getPreferenceStore();
    for (int i = 0; i < fCheckBoxes.size(); i++) {
      Button button = (Button) fCheckBoxes.get(i);
      String key = (String) button.getData();
      button.setSelection(store.getDefaultBoolean(key));
    }
    fDialectCombo.select(0);
//    fDialectCombo.setText(store.getDefaultString(PreferenceConstants.PROP_DIALECT));

    super.performDefaults();
  }

  /*
   * @see @see org.eclipse.jface.preference.PreferencePage#performOk()
   */
  public boolean performOk()
  {
    IPreferenceStore store = getPreferenceStore();
    for (int i = 0; i < fCheckBoxes.size(); i++) {
      Button button = (Button) fCheckBoxes.get(i);
      String key = (String) button.getData();
      store.setValue(key, button.getSelection());
    }
    store.setValue(PreferenceConstants.PROP_DIALECT, fDialectCombo.getText());

    CZTPlugin.getDefault().savePluginPreferences();

    return super.performOk();
  }
}
