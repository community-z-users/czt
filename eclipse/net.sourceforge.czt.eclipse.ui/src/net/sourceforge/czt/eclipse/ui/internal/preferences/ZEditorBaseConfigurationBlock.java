/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import java.util.ArrayList;

import net.sourceforge.czt.eclipse.ui.internal.editors.PixelConverter;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.osgi.util.NLS;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.FontMetrics;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Link;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.dialogs.PreferencesUtil;

/**
 * @author Chengdong Xu
 */
public class ZEditorBaseConfigurationBlock extends AbstractConfigurationBlock
{
  private ColorSelector fMatchingBracketsColorEditor;

//  private Button fAppearanceColorDefault;

  private FontMetrics fFontMetrics;

  public ZEditorBaseConfigurationBlock(PreferencePage mainPreferencePage,
      OverlayPreferenceStore store)
  {
    super(store, mainPreferencePage);
    getPreferenceStore().addKeys(createOverlayStoreKeys());
  }

  private OverlayPreferenceStore.OverlayKey[] createOverlayStoreKeys()
  {
    ArrayList<OverlayPreferenceStore.OverlayKey> overlayKeys = new ArrayList<OverlayPreferenceStore.OverlayKey>();

    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.BOOLEAN,
        ZEditorConstants.PARSING_ENABLED));
    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.STRING,
        ZEditorConstants.REPORT_PROBLEMS));
    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.BOOLEAN,
        ZEditorConstants.MATCHING_BRACKETS));
    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.STRING,
        ZEditorConstants.MATCHING_BRACKETS_COLOR));
    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.BOOLEAN,
        ZEditorConstants.SYNC_OUTLINE_ON_CURSOR_MOVE));
    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.BOOLEAN,
        ZEditorConstants.SHOW_HOVER));
    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.BOOLEAN,
        ZEditorConstants.MARK_OCCURRENCES));

    OverlayPreferenceStore.OverlayKey[] keys = new OverlayPreferenceStore.OverlayKey[overlayKeys
        .size()];
    overlayKeys.toArray(keys);
    return keys;
  }

  /**
   * Creates page for appearance preferences.
   * 
   * @param parent the parent composite
   * @return the control for the preference page
   */
  public Control createControl(Composite parent)
  {
    initializeDialogUnits(parent);

    Composite composite = new Composite(parent, SWT.NONE);
    composite.setLayout(GridLayoutFactory.fillDefaults().create());

    createHeader(composite);
    createAppearancePage(composite);

    return composite;
  }

  private void createHeader(Composite contents)
  {
    final Shell shell = contents.getShell();
    String text = PreferencesMessages.ZEditorBasePreferencePage_note_link;
    Link link = new Link(contents, SWT.NONE);
    link.setText(text);
    link.addSelectionListener(new SelectionAdapter()
    {
      public void widgetSelected(SelectionEvent e)
      {
        PreferencesUtil.createPreferenceDialogOn(shell,
            "org.eclipse.ui.preferencePages.GeneralTextEditor", null, null); //$NON-NLS-1$
      }
    });
    // TODO replace by link-specific tooltips when
    // bug https://bugs.eclipse.org/bugs/show_bug.cgi?id=88866 gets fixed
    link
        .setToolTipText(PreferencesMessages.ZEditorBasePreferencePage_note_link_tooltip);

    GridData gridData = new GridData(SWT.FILL, SWT.BEGINNING, true, false);
    gridData.widthHint = 150; // only expand further if anyone else requires it
    link.setLayoutData(gridData);

    addFiller(contents);
  }

  private void addFiller(Composite composite)
  {
    PixelConverter pixelConverter = new PixelConverter(composite);

    Label filler = new Label(composite, SWT.LEFT);
    GridData gd = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
    gd.horizontalSpan = 2;
    gd.heightHint = pixelConverter.convertHeightInCharsToPixels(1) / 2;
    filler.setLayoutData(gd);
  }

  /**
   * Returns the number of pixels corresponding to the width of the given
   * number of characters.
   * <p>
   * This method may only be called after <code>initializeDialogUnits</code>
   * has been called.
   * </p>
   * <p>
   * Clients may call this framework method, but should not override it.
   * </p>
   * 
   * @param chars
   *            the number of characters
   * @return the number of pixels
   */
  protected int convertWidthInCharsToPixels(int chars)
  {
    // test for failure to initialize for backward compatibility
    if (fFontMetrics == null)
      return 0;
    return Dialog.convertWidthInCharsToPixels(fFontMetrics, chars);
  }

  /**
   * Returns the number of pixels corresponding to the height of the given
   * number of characters.
   * <p>
   * This method may only be called after <code>initializeDialogUnits</code>
   * has been called.
   * </p>
   * <p>
   * Clients may call this framework method, but should not override it.
   * </p>
   * 
   * @param chars
   *            the number of characters
   * @return the number of pixels
   */
  protected int convertHeightInCharsToPixels(int chars)
  {
    // test for failure to initialize for backward compatibility
    if (fFontMetrics == null)
      return 0;
    return Dialog.convertHeightInCharsToPixels(fFontMetrics, chars);
  }

  private Control createAppearancePage(Composite parent)
  {

    Composite appearanceComposite = new Composite(parent, SWT.NONE);
    appearanceComposite.setLayout(GridLayoutFactory.fillDefaults().numColumns(2).create());

    String label;

    label = PreferencesMessages.ZEditorBasePreferencePage_parsing_enable;
    Button parseEnableButton = addCheckBox(appearanceComposite, label,
        ZEditorConstants.PARSING_ENABLED, 0);

    label = PreferencesMessages.ZEditorBasePreferencePage_report_problems_on_save;
    Button reportOnSaveButton = addRadioButton(appearanceComposite, label,
        ZEditorConstants.REPORT_PROBLEMS, ZEditorConstants.REPORT_PROBLEMS_ON_SAVE, 0);
    
    label = PreferencesMessages.ZEditorBasePreferencePage_report_problems_while_editing;
    Button reportWhileEditButton = addRadioButton(appearanceComposite, label,
        ZEditorConstants.REPORT_PROBLEMS, ZEditorConstants.REPORT_PROBLEMS_WHILE_EDITING, 0);
    
    createDependency(parseEnableButton, new Button[]{reportOnSaveButton, reportWhileEditButton});
    
    String text = NLS.bind(PreferencesMessages.ZEditorBasePreferencePage_compiler_link,
        "net.sourceforge.czt.eclipse.ui.preferences.compiler"); //$NON-NLS-1$
    Link link = addLink(appearanceComposite, text, INDENT);
    link.setToolTipText(PreferencesMessages.ZEditorBasePreferencePage_compiler_link_tooltip);
    
    Label spacer = new Label(appearanceComposite, SWT.LEFT);
    GridData gd = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
    gd.horizontalSpan = 2;
    gd.heightHint = convertHeightInCharsToPixels(1) / 2;
    spacer.setLayoutData(gd);

    label = PreferencesMessages.ZEditorBasePreferencePage_matching_brackets;
    Button matchingBracketsButton = addCheckBox(appearanceComposite, label,
        ZEditorConstants.MATCHING_BRACKETS, 0);

    Label l = new Label(appearanceComposite, SWT.LEFT);
    l.setText(PreferencesMessages.ZEditorBasePreferencePage_matching_brackets_color);
    gd = new GridData(GridData.HORIZONTAL_ALIGN_BEGINNING);
    gd.horizontalIndent = INDENT;
    l.setLayoutData(gd);

    fMatchingBracketsColorEditor = new ColorSelector(appearanceComposite);
    Button foregroundColorButton = fMatchingBracketsColorEditor.getButton();
    gd = new GridData(GridData.FILL_HORIZONTAL);
    gd.horizontalAlignment = GridData.BEGINNING;
    foregroundColorButton.setLayoutData(gd);

    foregroundColorButton.addSelectionListener(new SelectionListener()
    {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        String key = ZEditorConstants.MATCHING_BRACKETS_COLOR;
        PreferenceConverter.setValue(getPreferenceStore(), key,
            fMatchingBracketsColorEditor.getColorValue());
      }
    });
    
    createDependency(matchingBracketsButton, foregroundColorButton);
    
    //  another spacer
    l = new Label(appearanceComposite, SWT.LEFT);
    gd = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
    gd.horizontalSpan = 2;
    gd.heightHint = convertHeightInCharsToPixels(1) / 2;
    l.setLayoutData(gd);
    
    label = PreferencesMessages.ZEditorBasePreferencePage_sync_outline_on_cursor_move;
    addCheckBox(appearanceComposite, label,
        ZEditorConstants.SYNC_OUTLINE_ON_CURSOR_MOVE, 0);
    
    //  another spacer
    l = new Label(appearanceComposite, SWT.LEFT);
    gd = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
    gd.horizontalSpan = 2;
    gd.heightHint = convertHeightInCharsToPixels(1) / 2;
    l.setLayoutData(gd);
    
    label = PreferencesMessages.ZEditorBasePreferencePage_show_text_hover;
    addCheckBox(appearanceComposite, label,
        ZEditorConstants.SHOW_HOVER, 0);
    
    //  another spacer
    l = new Label(appearanceComposite, SWT.LEFT);
    gd = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
    gd.horizontalSpan = 2;
    gd.heightHint = convertHeightInCharsToPixels(1) / 2;
    l.setLayoutData(gd);
    
    label = PreferencesMessages.ZEditorBasePreferencePage_mark_occurrences;
    addCheckBox(appearanceComposite, label,
        ZEditorConstants.MARK_OCCURRENCES, 0);
    
    return appearanceComposite;
  }

  private Link addLink(Composite composite, String text, int indent)
  {
    GridData gd;
    final Link link = new Link(composite, SWT.NONE);
    link.setText(text);
    gd = new GridData(SWT.FILL, SWT.BEGINNING, true, false);
    gd.widthHint = 300; // don't get wider initially
    gd.horizontalSpan = 2;
    gd.horizontalIndent = indent;
    link.setLayoutData(gd);
    link.addSelectionListener(new SelectionAdapter()
    {
      public void widgetSelected(SelectionEvent e)
      {
        PreferencesUtil.createPreferenceDialogOn(link.getShell(), e.text, null,
            null);
      }
    });
    
    return link;
  }

  private void updateColorSelector()
  {
    String key = ZEditorConstants.MATCHING_BRACKETS_COLOR;
    RGB rgb = PreferenceConverter.getColor(getPreferenceStore(), key);
    fMatchingBracketsColorEditor.setColorValue(rgb);
  }

  /*
   * @see org.eclipse.jdt.internal.ui.preferences.IPreferenceConfigurationBlock#initialize()
   */
  public void initialize()
  {
    super.initialize();
    updateColorSelector();
  }

  /*
   * @see org.eclipse.jdt.internal.ui.preferences.IPreferenceConfigurationBlock#performDefaults()
   */
  public void performDefaults()
  {
    super.performDefaults();
    updateColorSelector();
  }

  /**
   * Initializes the computation of horizontal and vertical dialog units based
   * on the size of current font.
   * <p>
   * This method must be called before any of the dialog unit based conversion
   * methods are called.
   * </p>
   * 
   * @param testControl
   *            a control from which to obtain the current font
   */
  protected void initializeDialogUnits(Control testControl)
  {
    // Compute and store a font metric
    GC gc = new GC(testControl);
    gc.setFont(JFaceResources.getDialogFont());
    fFontMetrics = gc.getFontMetrics();
    gc.dispose();
  }
}