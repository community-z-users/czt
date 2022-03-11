/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import java.util.ArrayList;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

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
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

/**
 * @author Chengdong Xu
 *
 */
public class ZEditorFoldingPreferencePage extends PreferencePage
    implements
      IWorkbenchPreferencePage
{

  private Button fEnableFoldingButton;
  private Group elementsGroup;
  private ArrayList<Button> fCheckBoxes;

  //private ArrayList<Button> fRadioButtons;

  //private ArrayList fTextControls;

  public ZEditorFoldingPreferencePage()
  {
    super();
    setPreferenceStore(CztUIPlugin.getDefault().getPreferenceStore());
    setDescription(PreferencesMessages.ZEditorPreferencePage_folding_description);

    //fRadioButtons = new ArrayList<Button>();
    fCheckBoxes = new ArrayList<Button>();
    //fTextControls = new ArrayList();
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

  private Button createCheckBox(Composite parent, String label, String tooltip,
      String key)
  {
    GridData gd = new GridData(GridData.HORIZONTAL_ALIGN_FILL);

    Button button = new Button(parent, SWT.CHECK);
    button.setText(label);
    button.setToolTipText(tooltip);
    button.setData(key);
    button.setLayoutData(gd);

    button.setSelection(getPreferenceStore().getBoolean(key));

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
    
    fEnableFoldingButton = createCheckBox(
        result,
        PreferencesMessages.ZEditorPreferencePage_folding_enable,
        PreferencesMessages.ZEditorPreferencePage_folding_enable_tooltip,
        ZEditorConstants.FOLDING_ENABLED);
    fEnableFoldingButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
    fEnableFoldingButton.addSelectionListener(new SelectionListener() {
      public void widgetSelected(SelectionEvent se) {
        doFoldingButtonSelected();
      }
      
      public void widgetDefaultSelected(SelectionEvent se) {
        doFoldingButtonSelected();
      }
    });

    elementsGroup = new Group(result, SWT.NONE);
    elementsGroup.setLayout(new GridLayout());
    elementsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
    elementsGroup
        .setText(PreferencesMessages.ZEditorPreferencePage_folding_enable_elements);
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_narrative,
        null,
        ZEditorConstants.FOLDING_NARRATIVE));
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_directive,
        null,
        ZEditorConstants.FOLDING_ZCHAR));
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_zed,
        null,
        ZEditorConstants.FOLDING_ZED));
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_section,
        null,
        ZEditorConstants.FOLDING_ZSECTION));
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_ax,
        null,
        ZEditorConstants.FOLDING_AX));
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_sch,
        null,
        ZEditorConstants.FOLDING_SCH));
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_genax,
        null,
        ZEditorConstants.FOLDING_GENAX));
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_gensch,
        null,
        ZEditorConstants.FOLDING_GENSCH));
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_theorem,
        null,
        ZEditorConstants.FOLDING_THEOREM));
    fCheckBoxes.add(createCheckBox(
        elementsGroup,
        PreferencesMessages.ZEditorPreferencePage_folding_element_proofscript,
        null,
        ZEditorConstants.FOLDING_PROOFSCRIPT));
    
    doFoldingButtonSelected();
    
    Dialog.applyDialogFont(result);
    return result;
  }
  
  // Bug in SelectionListener? the method can not have the same name as the one in SelectionListener
  private void doFoldingButtonSelected() {
    boolean enabled = fEnableFoldingButton.getSelection();
    for (Button button : fCheckBoxes)
      button.setEnabled(enabled);
  }
  
  /*
   * @see @see org.eclipse.jface.preference.PreferencePage#performDefaults()
   */
  protected void performDefaults()
  {
    IPreferenceStore store = getPreferenceStore();
    
    fEnableFoldingButton.setSelection(store.getDefaultBoolean((String)fEnableFoldingButton.getData()));
    for (int i = 0; i < fCheckBoxes.size(); i++) {
      Button button = fCheckBoxes.get(i);
      String key = (String) button.getData();
      button.setSelection(store.getDefaultBoolean(key));
    }

    // force the checkboxes to response as setting selection in code has no effect
    doFoldingButtonSelected();
    
    super.performDefaults();
  }

  /*
   * @see @see org.eclipse.jface.preference.PreferencePage#performOk()
   */
  @SuppressWarnings("deprecation")
  // TODO: deprecated!!
public boolean performOk()
  {
    IPreferenceStore store = getPreferenceStore();
    store.setValue((String)fEnableFoldingButton.getData(), fEnableFoldingButton.getSelection());
    for (int i = 0; i < fCheckBoxes.size(); i++) {
      Button button = (Button) fCheckBoxes.get(i);
      String key = (String) button.getData();
      store.setValue(key, button.getSelection());
    }

    CztUIPlugin.getDefault().savePluginPreferences();

    return super.performOk();
  }
}
