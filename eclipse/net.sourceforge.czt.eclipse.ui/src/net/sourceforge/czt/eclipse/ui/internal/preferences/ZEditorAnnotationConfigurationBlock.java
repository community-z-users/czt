/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.internal.preferences;

import java.util.ArrayList;

import net.sourceforge.czt.eclipse.ui.internal.editors.PixelConverter;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.FontMetrics;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Link;
import org.eclipse.ui.dialogs.PreferencesUtil;

/**
 * @author Chengdong Xu
 */
public class ZEditorAnnotationConfigurationBlock
    extends
      AbstractConfigurationBlock
{
  /**
   * @param store
   * @param mainPreferencePage
   */
  
  private Combo fSchemaBoxStyleCombo;
  private ColorSelector fSchemaBoxLineColorEditor;
  private Combo fSchemaBoxLineWidthCombo;

//  private Button fAppearanceColorDefault;

  private FontMetrics fFontMetrics;

  public ZEditorAnnotationConfigurationBlock(PreferencePage mainPreferencePage,
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
        ZEditorConstants.ANNOTATION_SCHEMABOX_ENABLE));
    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.STRING,
        ZEditorConstants.ANNOTATION_SCHEMABOX_STYLE));
    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.STRING,
        ZEditorConstants.ANNOTATION_SCHEMABOX_LINE_COLOR));
    overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
        OverlayPreferenceStore.INT,
        ZEditorConstants.ANNOTATION_SCHEMABOX_LINE_WIDTH));

    OverlayPreferenceStore.OverlayKey[] keys = new OverlayPreferenceStore.OverlayKey[overlayKeys
        .size()];
    overlayKeys.toArray(keys);
    return keys;
  }
  
  /**
   * Creates page for annotation preferences.
   * 
   * @param parent the parent composite
   * @return the control for the preference page
   * 
   * @see net.sourceforge.czt.eclipse.ui.internal.preferences.IPreferenceConfigurationBlock
   * #createControl(org.eclipse.swt.widgets.Composite)
   */
  public Control createControl(Composite parent)
  {
    initializeDialogUnits(parent);

    Composite composite = new Composite(parent, SWT.NONE);
    composite.setLayout(GridLayoutFactory.fillDefaults().create());

    createHeader(composite);
    createAnnotationPage(composite);

    return composite;
  }

  private void createHeader(Composite contents)
  {
//    final Shell shell = contents.getShell();
    String text = PreferencesMessages.ZEditorPreferencePage_annotation_note_link;
    Link link = new Link(contents, SWT.NONE);
    link.setText(text);
    // TODO replace by link-specific tooltips when
    // bug https://bugs.eclipse.org/bugs/show_bug.cgi?id=88866 gets fixed
    link
        .setToolTipText(PreferencesMessages.ZEditorPreferencePage_annotation_note_link_tooltip);

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

  private Control createAnnotationPage(Composite parent)
  {

    Composite annotationComposite = new Composite(parent, SWT.NONE);
    annotationComposite.setLayout(GridLayoutFactory.fillDefaults().numColumns(2).create());
    annotationComposite.setLayoutData(GridDataFactory.fillDefaults().grab(true, false).create());

    String label;

    Group schemaBoxGroup = new Group(annotationComposite, SWT.NONE);
    schemaBoxGroup.setLayout(GridLayoutFactory.swtDefaults().numColumns(2).create());
    schemaBoxGroup.setLayoutData(GridDataFactory.fillDefaults().span(2, 1).grab(true, false).create());
    schemaBoxGroup.setText(PreferencesMessages.ZEditorPreferencePage_annotation_schema_box);
    
    label = PreferencesMessages.ZEditorPreferencePage_annotation_schema_box_enable;
    Button schemaBoxEnableButton = addCheckBox(schemaBoxGroup, label,
        ZEditorConstants.ANNOTATION_SCHEMABOX_ENABLE, 0);

    label = PreferencesMessages.ZEditorPreferencePage_annotation_schema_box_style;
    Label boxStyleLabel = new Label(schemaBoxGroup, SWT.LEFT);
    boxStyleLabel.setText(label);
    boxStyleLabel.setLayoutData(GridDataFactory.swtDefaults().create());

    fSchemaBoxStyleCombo = new Combo(schemaBoxGroup, SWT.NONE);
    fSchemaBoxStyleCombo.setLayoutData(GridDataFactory.swtDefaults().create());
    fSchemaBoxStyleCombo.setItems(new String[]{PreferencesMessages.ZEditorPreferencePage_annotation_schema_box_style_1, PreferencesMessages.ZEditorPreferencePage_annotation_schema_box_style_2});
    fSchemaBoxStyleCombo.addSelectionListener(new SelectionListener() {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        String key = ZEditorConstants.ANNOTATION_SCHEMABOX_STYLE;
        if (fSchemaBoxStyleCombo.getSelectionIndex() == 0)
          getPreferenceStore().setValue(key, ZEditorConstants.ANNOTATION_SCHEMABOX_STYLE_1);
        else if (fSchemaBoxStyleCombo.getSelectionIndex() == 1)
          getPreferenceStore().setValue(key, ZEditorConstants.ANNOTATION_SCHEMABOX_STYLE_2);
      }
    });
    
    
    
    label = PreferencesMessages.ZEditorPreferencePage_annotation_schema_box_line_color;
    Label boxLineColorLabel = new Label(schemaBoxGroup, SWT.LEFT);
    boxLineColorLabel.setLayoutData(GridDataFactory.swtDefaults().create());
    boxLineColorLabel.setText(label);
    
    fSchemaBoxLineColorEditor = new ColorSelector(schemaBoxGroup);
    Button boxLineColorButton = fSchemaBoxLineColorEditor.getButton();
    boxLineColorButton.setLayoutData(GridDataFactory.swtDefaults().create());
    
    boxLineColorButton.addSelectionListener(new SelectionListener()
    {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        String key = ZEditorConstants.ANNOTATION_SCHEMABOX_LINE_COLOR;
        PreferenceConverter.setValue(getPreferenceStore(), key,
            fSchemaBoxLineColorEditor.getColorValue());
      }
    });
    
    label = PreferencesMessages.ZEditorPreferencePage_annotation_schema_box_line_width;
    Label boxLineWidthLabel = new Label(schemaBoxGroup, SWT.LEFT);
    boxLineWidthLabel.setLayoutData(GridDataFactory.swtDefaults().create());
    boxLineWidthLabel.setText(label);
    
    fSchemaBoxLineWidthCombo = new Combo(schemaBoxGroup, SWT.NONE);
    fSchemaBoxLineWidthCombo.setLayoutData(GridDataFactory.swtDefaults().create());
    fSchemaBoxLineWidthCombo.setItems(new String[]{ "0", "1", "2", "3", "4", "5" });
    fSchemaBoxLineWidthCombo.addSelectionListener(new SelectionListener() {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        String key = ZEditorConstants.ANNOTATION_SCHEMABOX_LINE_WIDTH;
        getPreferenceStore().setValue(key, fSchemaBoxLineWidthCombo.getSelectionIndex());
      }
    });
    
    createDependency(schemaBoxEnableButton, new Control[] { fSchemaBoxStyleCombo, boxLineColorButton, fSchemaBoxLineWidthCombo });
    
    return annotationComposite;
  }

  protected Link addLink(Composite composite, String text, int indent)
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

  private void updateUnManagedControl()
  {
    String key = ZEditorConstants.ANNOTATION_SCHEMABOX_STYLE;
    String style = getPreferenceStore().getString(key);
    if (ZEditorConstants.ANNOTATION_SCHEMABOX_STYLE_1.equals(style))
      fSchemaBoxStyleCombo.select(0);
    else if (ZEditorConstants.ANNOTATION_SCHEMABOX_STYLE_2.equals(style))
      fSchemaBoxStyleCombo.select(1);
    else
      fSchemaBoxStyleCombo.select(-1);
    
    key = ZEditorConstants.ANNOTATION_SCHEMABOX_LINE_COLOR;
    fSchemaBoxLineColorEditor.setColorValue(PreferenceConverter.getColor(getPreferenceStore(), key));
    
    key = ZEditorConstants.ANNOTATION_SCHEMABOX_LINE_WIDTH;
    fSchemaBoxLineWidthCombo.select(getPreferenceStore().getInt(key));
  }

  /*
   * @see org.eclipse.jdt.internal.ui.preferences.IPreferenceConfigurationBlock#initialize()
   */
  public void initialize()
  {
    super.initialize();
    updateUnManagedControl();
  }

  /*
   * @see org.eclipse.jdt.internal.ui.preferences.IPreferenceConfigurationBlock#performDefaults()
   */
  public void performDefaults()
  {
    super.performDefaults();
    updateUnManagedControl();
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
