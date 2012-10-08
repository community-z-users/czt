/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.internal.editors.FontUpdater;
import net.sourceforge.czt.eclipse.ui.internal.editors.PixelConverter;
import net.sourceforge.czt.eclipse.ui.internal.editors.ZSourceViewer;
import net.sourceforge.czt.eclipse.ui.internal.util.CZTColorManager;
import net.sourceforge.czt.eclipse.ui.internal.util.IZColorConstants;
import net.sourceforge.czt.eclipse.ui.internal.util.IZFileType;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.layout.GridLayoutFactory;
import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerSorter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.FontMetrics;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Link;
import org.eclipse.swt.widgets.ScrollBar;
import org.eclipse.swt.widgets.Scrollable;
import org.eclipse.ui.dialogs.PreferencesUtil;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;

/**
 * Configures Z Editor syntax coloring preferences.
 * 
 * @author Chengdong Xu
 */
public class ZEditorSyntaxColoringConfigurationBlock
    extends
      AbstractConfigurationBlock
{

  /**
   * Item in the highlighting color list.
   */
  private static class HighlightingColorListItem
  {
    /** Display name */
    private String fDisplayName;

    /** Foreground preference key */
    private String fForegroundKey;

    /** Bold preference key */
    private String fBoldKey;

    /** Italic preference key */
    private String fItalicKey;

    /**
     * Strikethrough preference key.
     */
    private String fStrikethroughKey;

    /**
     * Underline preference key.
     */
    private String fUnderlineKey;

    /**
     * Initialize the item with the given values.
     * @param displayName the display name
     * @param colorKey the color preference key
     * @param boldKey the bold preference key
     * @param italicKey the italic preference key
     * @param strikethroughKey the strikethrough preference key
     * @param underlineKey the underline preference key
     */
    public HighlightingColorListItem(String displayName, String foregroundKey,
        String boldKey, String italicKey, String strikethroughKey,
        String underlineKey)
    {
      fDisplayName = displayName;
      fForegroundKey = foregroundKey;
      fBoldKey = boldKey;
      fItalicKey = italicKey;
      fStrikethroughKey = strikethroughKey;
      fUnderlineKey = underlineKey;
    }

    /**
     * @return the display name
     */
    public String getDisplayName()
    {
      return fDisplayName;
    }

    /**
     * @return the foreground preference key
     */
    public String getForegroundKey()
    {
      return fForegroundKey;
    }

    /**
     * @return the bold preference key
     */
    public String getBoldKey()
    {
      return fBoldKey;
    }

    /**
     * @return the bold preference key
     */
    public String getItalicKey()
    {
      return fItalicKey;
    }

    /**
     * @return the strikethrough preference key
     */
    public String getStrikethroughKey()
    {
      return fStrikethroughKey;
    }

    /**
     * @return the underline preference key
     */
    public String getUnderlineKey()
    {
      return fUnderlineKey;
    }
  }

  /**
   * Iterm in the semantic highlighting color list
   */
  private static class SemanticHighlightingColorListItem
      extends
        HighlightingColorListItem
  {

    /** Enablement preference key */
    private final String fEnableKey;

    /**
     * Initialize the item with the given values.
     * @param displayName the display name
     * @param colorKey the color preference key
     * @param boldKey the bold preference key
     * @param italicKey the italic preference key
     * @param strikethroughKey the strikethroughKey preference key
     * @param underlineKey the underlineKey preference key
     * @param enableKey the enable preference key
     */
    public SemanticHighlightingColorListItem(String displayName,
        String foregroundKey, String boldKey, String italicKey,
        String strikethroughKey, String underlineKey, String enableKey)
    {
      super(displayName, foregroundKey, boldKey, italicKey, strikethroughKey,
          underlineKey);
      fEnableKey = enableKey;
    }

    /**
     * @return the enablement preference key
     */
    public String getEnableKey()
    {
      return fEnableKey;
    }
  }

  /**
   * Color list label provider.
   */
  private class ColorListLabelProvider extends LabelProvider
  {
    /*
     * @see org.eclipse.jface.viewers.ILabelProvider#getText(java.lang.Object)
     */
    public String getText(Object element)
    {
      if (element instanceof HighlightingColorListItem)
        return ((HighlightingColorListItem) element).getDisplayName();
      
      return (String) element;
    }
  }

  /**
   * Color list content provider.
   */
  private class ColorListContentProvider implements ITreeContentProvider
  {

    /*
     * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
     */
    public Object[] getElements(Object inputElement)
    {
      return new Object[]{ fZCodeCategory, fListModel.get(3), fListModel.get(4) };
    }

    /*
     * @see org.eclipse.jface.viewers.IContentProvider#dispose()
     */
    public void dispose()
    {
    }

    /*
     * @see org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface.viewers.Viewer, java.lang.Object, java.lang.Object)
     */
    public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
    {
    }

    public Object[] getChildren(Object parentElement)
    {
      if (parentElement instanceof String) {
        String entry = (String) parentElement;
        if (fZCodeCategory.equals(entry))
          return fListModel.subList(0, 3).toArray();
      }
      
      return new Object[0];
    }

    public Object getParent(Object element)
    {
      if (element instanceof String)
        return null;
      
      int index = fListModel.indexOf(element);
      if (index < 3)
        return fZCodeCategory;
      
      return null;
    }

    public boolean hasChildren(Object element)
    {
      return element instanceof String;
    }
  }

  /**
   * Preference key suffix for foreground preferences.
   */
  private static final String FOREGROUND = ZEditorConstants.SUFFIX_FOREGROUND;
  
  /**
   * Preference key suffix for bold preferences.
   */
  private static final String BOLD = ZEditorConstants.SUFFIX_BOLD;

  /**
   * Preference key suffix for italic preferences.
   */
  private static final String ITALIC = ZEditorConstants.SUFFIX_ITALIC;

  /**
   * Preference key suffix for strikethrough preferences.
   */
  private static final String STRIKETHROUGH = ZEditorConstants.SUFFIX_STRIKETHROUGH;

  /**
   * Preference key suffix for underline preferences.
   */
  private static final String UNDERLINE = ZEditorConstants.SUFFIX_UNDERLINE;

  /**
   * The keys of the overlay store. 
   */
  private final String[][] fSyntaxColorListModel = new String[][]{
      {PreferencesMessages.ZEditorPreferencePage_keywords,
          IZColorConstants.CZT_KEYWORD},
      {PreferencesMessages.ZEditorPreferencePage_operators,
          IZColorConstants.CZT_OPERATOR},
      {PreferencesMessages.ZEditorPreferencePage_default,
          IZColorConstants.CZT_DEFAULT},
      {PreferencesMessages.ZEditorPreferencePage_comments,
          IZColorConstants.CZT_COMMENT},
      {PreferencesMessages.ZEditorPreferencePage_narratives,
          IZColorConstants.CZT_NARRATIVE},};

  private final String fZCodeCategory = PreferencesMessages.ZEditorPreferencePage_coloring_category_code;

  /**
   * Check box for enable preference.
   */
  private Button fEnableCheckbox;
  
  /**
   * Label for foreground preference
   */
  private Label fForegroundColorEditorLabel;
  
  /**
   * Color selector for foreground preference
   */
  private ColorSelector fSyntaxForegroundColorEditor;
  
  /**
   * Check box for bold preference.
   */
  private Button fBoldCheckBox;

  /**
   * Check box for italic preference.
   */
  private Button fItalicCheckBox;

  /**
   * Check box for strikethrough preference.
   */
  private Button fStrikethroughCheckBox;

  /**
   * Check box for underline preference.
   */
  private Button fUnderlineCheckBox;

  /**
   * Highlighting color list
   */
  private final java.util.List<HighlightingColorListItem> fListModel = new ArrayList<HighlightingColorListItem>();

  /**
   * Highlighting color list viewer
   */
  private StructuredViewer fListViewer;

  /**
   * The previewer.
   */
  private ZSourceViewer fPreviewViewer;

  /**
   * The color manager.
   */
  private CZTColorManager fColorManager;

  /**
   * The font metrics.
   */
  private FontMetrics fFontMetrics;

  /**
   * @param store the overlay preference store
   */
  public ZEditorSyntaxColoringConfigurationBlock(OverlayPreferenceStore store)
  {
    super(store);

    fColorManager = new CZTColorManager();

    for (int i = 0, n = fSyntaxColorListModel.length; i < n; i++)
      fListModel.add(new HighlightingColorListItem(fSyntaxColorListModel[i][0],
          fSyntaxColorListModel[i][1] + FOREGROUND, fSyntaxColorListModel[i][1] + BOLD,
          fSyntaxColorListModel[i][1] + ITALIC, fSyntaxColorListModel[i][1]
              + STRIKETHROUGH, fSyntaxColorListModel[i][1] + UNDERLINE));

    store.addKeys(createOverlayStoreKeys());
  }

  private OverlayPreferenceStore.OverlayKey[] createOverlayStoreKeys()
  {

    List<OverlayPreferenceStore.OverlayKey> overlayKeys = new ArrayList<OverlayPreferenceStore.OverlayKey>();

    for (int i = 0, n = fListModel.size(); i < n; i++) {
      HighlightingColorListItem item = (HighlightingColorListItem) fListModel
          .get(i);
      overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
          OverlayPreferenceStore.STRING, item.getForegroundKey()));
      overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
          OverlayPreferenceStore.BOOLEAN, item.getBoldKey()));
      overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
          OverlayPreferenceStore.BOOLEAN, item.getItalicKey()));
      overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
          OverlayPreferenceStore.BOOLEAN, item.getStrikethroughKey()));
      overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
          OverlayPreferenceStore.BOOLEAN, item.getUnderlineKey()));

      if (item instanceof SemanticHighlightingColorListItem)
        overlayKeys.add(new OverlayPreferenceStore.OverlayKey(
            OverlayPreferenceStore.BOOLEAN,
            ((SemanticHighlightingColorListItem) item).getEnableKey()));
    }

    OverlayPreferenceStore.OverlayKey[] keys = new OverlayPreferenceStore.OverlayKey[overlayKeys
        .size()];
    overlayKeys.toArray(keys);
    return keys;
  }

  /**
   * Creates page for hover preferences.
   * 
   * @param parent the parent composite
   * @return the control for the preference page
   * @see net.sourceforge.czt.eclipse.ui.internal.preferences.IPreferenceConfigurationBlock#createControl(org.eclipse.swt.widgets.Composite)
   */
  public Control createControl(Composite parent)
  {
    initializeDialogUnits(parent);
    return createSyntaxPage(parent);
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
  private int convertWidthInCharsToPixels(int chars)
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
  private int convertHeightInCharsToPixels(int chars)
  {
    // test for failure to initialize for backward compatibility
    if (fFontMetrics == null)
      return 0;
    return Dialog.convertHeightInCharsToPixels(fFontMetrics, chars);
  }

  public void initialize()
  {
    super.initialize();

    fListViewer.setInput(fListModel);
    fListViewer.setSelection(new StructuredSelection(fZCodeCategory));
  }

  public void performDefaults()
  {
    super.performDefaults();

    handleSyntaxColorListSelection();

    //    uninstallSemanticHighlighting();
    //    installSemanticHighlighting();

    fPreviewViewer.invalidateTextPresentation();
  }

  /*
   * @see org.eclipse.jdt.internal.ui.preferences.IPreferenceConfigurationBlock#dispose()
   */
  public void dispose()
  {
    //    uninstallSemanticHighlighting();
    fColorManager.dispose();

    super.dispose();
  }

  private void handleSyntaxColorListSelection()
  {
    HighlightingColorListItem item = getHighlightingColorListItem();
    if (item == null) {
      fEnableCheckbox.setEnabled(false);
      fForegroundColorEditorLabel.setEnabled(false);
      fSyntaxForegroundColorEditor.getButton().setEnabled(false);
      fBoldCheckBox.setEnabled(false);
      fItalicCheckBox.setEnabled(false);
      fStrikethroughCheckBox.setEnabled(false);
      fUnderlineCheckBox.setEnabled(false);
      return;
    }
    RGB foreground = PreferenceConverter.getColor(getPreferenceStore(), item
        .getForegroundKey());
    fSyntaxForegroundColorEditor.setColorValue(foreground);
    //    RGB background = PreferenceConverter.getColor(getPreferenceStore(), item
    //        .getBackgroundKey());
    //    fSyntaxBackgroundColorEditor.setColorValue(background);
    fBoldCheckBox.setSelection(getPreferenceStore().getBoolean(
        item.getBoldKey()));
    fItalicCheckBox.setSelection(getPreferenceStore().getBoolean(
        item.getItalicKey()));
    fStrikethroughCheckBox.setSelection(getPreferenceStore().getBoolean(
        item.getStrikethroughKey()));
    fUnderlineCheckBox.setSelection(getPreferenceStore().getBoolean(
        item.getUnderlineKey()));
    if (item instanceof SemanticHighlightingColorListItem) {
      fEnableCheckbox.setEnabled(true);
      boolean enable = getPreferenceStore().getBoolean(
          ((SemanticHighlightingColorListItem) item).getEnableKey());
      fEnableCheckbox.setSelection(enable);
      fForegroundColorEditorLabel.setEnabled(enable);
      fSyntaxForegroundColorEditor.getButton().setEnabled(enable);
      fBoldCheckBox.setEnabled(enable);
      fItalicCheckBox.setEnabled(enable);
      fStrikethroughCheckBox.setEnabled(enable);
      fUnderlineCheckBox.setEnabled(enable);
    }
    else {
      fForegroundColorEditorLabel.setEnabled(true);
      fSyntaxForegroundColorEditor.getButton().setEnabled(true);
      fBoldCheckBox.setEnabled(true);
      fItalicCheckBox.setEnabled(true);
      fStrikethroughCheckBox.setEnabled(true);
      fUnderlineCheckBox.setEnabled(true);
      fEnableCheckbox.setEnabled(false);
      fEnableCheckbox.setSelection(true);
    }
  }

  private Control createSyntaxPage(final Composite parent)
  {

    Composite colorComposite = new Composite(parent, SWT.NONE);
    GridLayout layout = new GridLayout();
    layout.marginHeight = 0;
    layout.marginWidth = 0;
    colorComposite.setLayout(layout);

    Link link = new Link(colorComposite, SWT.NONE);
    link.setText(PreferencesMessages.ZEditorColoringConfigurationBlock_link);
    link.addSelectionListener(new SelectionAdapter()
    {
      public void widgetSelected(SelectionEvent e)
      {
        PreferencesUtil.createPreferenceDialogOn(parent.getShell(), e.text,
            null, null); //$NON-NLS-1$
      }
    });
    // TODO replace by link-specific tooltips when
    // bug https://bugs.eclipse.org/bugs/show_bug.cgi?id=88866 gets fixed
    //  link.setToolTipText(PreferencesMessages.JavaEditorColoringConfigurationBlock_link_tooltip); 

    GridData gridData = new GridData(SWT.FILL, SWT.BEGINNING, true, false);
    gridData.widthHint = 150; // only expand further if anyone else requires it
    gridData.horizontalSpan = 2;
    link.setLayoutData(gridData);

    addFiller(colorComposite, 1);

    Label label;
    label = new Label(colorComposite, SWT.LEFT);
    label.setText(PreferencesMessages.ZEditorPreferencePage_coloring_element);
    label.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

    Composite editorComposite = new Composite(colorComposite, SWT.NONE);
    layout = new GridLayout();
    layout.numColumns = 2;
    layout.marginHeight = 0;
    layout.marginWidth = 0;
    editorComposite.setLayout(layout);
    GridData gd = new GridData(SWT.FILL, SWT.FILL, true, false);
    editorComposite.setLayoutData(gd);

    fListViewer = new TreeViewer(editorComposite, SWT.SINGLE | SWT.BORDER);
    fListViewer.setLabelProvider(new ColorListLabelProvider());
    fListViewer.setContentProvider(new ColorListContentProvider());
    fListViewer.setSorter(new ViewerSorter()
    {
      public int category(Object element)
      {
        // don't sort the top level categories
        if (fZCodeCategory.equals(element))
          return 0;
        
//      to sort semantic settings after partition based ones:
//      if (element instanceof SemanticHighlightingColorListItem)
//          return 1;
        
        return 0;
      }
    });
    gd = new GridData(SWT.FILL, SWT.BEGINNING, true, true);
    gd.heightHint = convertHeightInCharsToPixels(9);
    int maxWidth = 0;
    for (HighlightingColorListItem item : fListModel) {
      maxWidth = Math.max(maxWidth, convertWidthInCharsToPixels(item
          .getDisplayName().length()));
    }
    ScrollBar vBar = ((Scrollable) fListViewer.getControl()).getVerticalBar();
    if (vBar != null)
      maxWidth += vBar.getSize().x * 3; // scrollbars and tree indentation guess
    gd.widthHint = maxWidth;

    fListViewer.getControl().setLayoutData(gd);

    Composite stylesComposite = new Composite(editorComposite, SWT.NONE);
    stylesComposite.setLayout(GridLayoutFactory.fillDefaults().numColumns(2).spacing(0, 0).create());
    stylesComposite.setLayoutData(new GridData(SWT.BEGINNING, SWT.BEGINNING, false, false));

    fEnableCheckbox = new Button(stylesComposite, SWT.CHECK);
    fEnableCheckbox.setText(PreferencesMessages.ZEditorPreferencePage_enable);
    gd = new GridData(GridData.FILL_HORIZONTAL);
    gd.horizontalAlignment = GridData.BEGINNING;
    gd.horizontalSpan = 2;
    fEnableCheckbox.setLayoutData(gd);

    fForegroundColorEditorLabel = new Label(stylesComposite, SWT.LEFT);
    fForegroundColorEditorLabel
        .setText(PreferencesMessages.ZEditorPreferencePage_foreground);
    gd = new GridData(GridData.HORIZONTAL_ALIGN_BEGINNING);
    gd.horizontalIndent = 20;
    fForegroundColorEditorLabel.setLayoutData(gd);

    fSyntaxForegroundColorEditor = new ColorSelector(stylesComposite);
    Button foregroundColorButton = fSyntaxForegroundColorEditor.getButton();
    gd = new GridData(GridData.HORIZONTAL_ALIGN_BEGINNING);
    foregroundColorButton.setLayoutData(gd);
    
    fBoldCheckBox = new Button(stylesComposite, SWT.CHECK);
    fBoldCheckBox.setText(PreferencesMessages.ZEditorPreferencePage_bold);
    gd = new GridData(GridData.HORIZONTAL_ALIGN_BEGINNING);
    gd.horizontalIndent = 20;
    gd.horizontalSpan = 2;
    fBoldCheckBox.setLayoutData(gd);

    fItalicCheckBox = new Button(stylesComposite, SWT.CHECK);
    fItalicCheckBox.setText(PreferencesMessages.ZEditorPreferencePage_italic);
    gd = new GridData(GridData.HORIZONTAL_ALIGN_BEGINNING);
    gd.horizontalIndent = 20;
    gd.horizontalSpan = 2;
    fItalicCheckBox.setLayoutData(gd);

    fStrikethroughCheckBox = new Button(stylesComposite, SWT.CHECK);
    fStrikethroughCheckBox
        .setText(PreferencesMessages.ZEditorPreferencePage_strikethrough);
    gd = new GridData(GridData.HORIZONTAL_ALIGN_BEGINNING);
    gd.horizontalIndent = 20;
    gd.horizontalSpan = 2;
    fStrikethroughCheckBox.setLayoutData(gd);

    fUnderlineCheckBox = new Button(stylesComposite, SWT.CHECK);
    fUnderlineCheckBox
        .setText(PreferencesMessages.ZEditorPreferencePage_underline);
    gd = new GridData(GridData.HORIZONTAL_ALIGN_BEGINNING);
    gd.horizontalIndent = 20;
    gd.horizontalSpan = 2;
    fUnderlineCheckBox.setLayoutData(gd);
    
    Composite spacer = new Composite(colorComposite, SWT.NONE);
    gd = new GridData();
    gd.heightHint = 0;
    spacer.setLayoutData(gd);

    label = new Label(colorComposite, SWT.LEFT);
    label.setText(PreferencesMessages.ZEditorPreferencePage_preview);
    label.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

    Control previewer = createPreviewer(colorComposite);
    gd = new GridData(GridData.FILL_BOTH);
    gd.widthHint = convertWidthInCharsToPixels(20);
    gd.heightHint = convertHeightInCharsToPixels(5);
    previewer.setLayoutData(gd);

    fListViewer.addSelectionChangedListener(new ISelectionChangedListener()
    {
      public void selectionChanged(SelectionChangedEvent event)
      {
        handleSyntaxColorListSelection();
      }
    });

    foregroundColorButton.addSelectionListener(new SelectionListener()
    {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        HighlightingColorListItem item = getHighlightingColorListItem();
        PreferenceConverter.setValue(getPreferenceStore(), item
            .getForegroundKey(), fSyntaxForegroundColorEditor.getColorValue());
      }
    });
    
    fBoldCheckBox.addSelectionListener(new SelectionListener()
    {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        HighlightingColorListItem item = getHighlightingColorListItem();
        getPreferenceStore().setValue(item.getBoldKey(),
            fBoldCheckBox.getSelection());
      }
    });

    fItalicCheckBox.addSelectionListener(new SelectionListener()
    {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        HighlightingColorListItem item = getHighlightingColorListItem();
        getPreferenceStore().setValue(item.getItalicKey(),
            fItalicCheckBox.getSelection());
      }
    });
    fStrikethroughCheckBox.addSelectionListener(new SelectionListener()
    {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        HighlightingColorListItem item = getHighlightingColorListItem();
        getPreferenceStore().setValue(item.getStrikethroughKey(),
            fStrikethroughCheckBox.getSelection());
      }
    });

    fUnderlineCheckBox.addSelectionListener(new SelectionListener()
    {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        HighlightingColorListItem item = getHighlightingColorListItem();
        getPreferenceStore().setValue(item.getUnderlineKey(),
            fUnderlineCheckBox.getSelection());
      }
    });

    fEnableCheckbox.addSelectionListener(new SelectionListener()
    {
      public void widgetDefaultSelected(SelectionEvent e)
      {
        // do nothing
      }

      public void widgetSelected(SelectionEvent e)
      {
        HighlightingColorListItem item = getHighlightingColorListItem();
        if (item instanceof SemanticHighlightingColorListItem) {
          boolean enable = fEnableCheckbox.getSelection();
          getPreferenceStore()
              .setValue(
                  ((SemanticHighlightingColorListItem) item).getEnableKey(),
                  enable);
          fEnableCheckbox.setSelection(enable);
          fForegroundColorEditorLabel.setEnabled(enable);
          fSyntaxForegroundColorEditor.getButton().setEnabled(enable);
          fBoldCheckBox.setEnabled(enable);
          fItalicCheckBox.setEnabled(enable);
          fStrikethroughCheckBox.setEnabled(enable);
          fUnderlineCheckBox.setEnabled(enable);
          //          uninstallSemanticHighlighting();
          //          installSemanticHighlighting();
        }
      }
    });

    colorComposite.layout(false);

    return colorComposite;
  }

  private void addFiller(Composite composite, int horizontalSpan)
  {
    PixelConverter pixelConverter = new PixelConverter(composite);
    Label filler = new Label(composite, SWT.LEFT);
    GridData gd = new GridData(GridData.HORIZONTAL_ALIGN_FILL);
    gd.horizontalSpan = horizontalSpan;
    gd.heightHint = pixelConverter.convertHeightInCharsToPixels(1) / 2;
    filler.setLayoutData(gd);
  }

  /*
   * Create the previewer control
   */
  private Control createPreviewer(Composite parent)
  {

    IPreferenceStore generalTextStore = EditorsUI.getPreferenceStore();
    IPreferenceStore store = new ChainedPreferenceStore(new IPreferenceStore[]{
        getPreferenceStore(), generalTextStore});
    fPreviewViewer = new ZSourceViewer(parent, null, null, false, SWT.V_SCROLL
        | SWT.H_SCROLL | SWT.BORDER, store);
    SimpleZSourceViewerConfiguration configuration = new SimpleZSourceViewerConfiguration(
        fColorManager, store, null, IZPartitions.Z_PARTITIONING, false);
    fPreviewViewer.configure(configuration);
    
    // enable font updates
    FontUpdater.enableFor(fPreviewViewer, configuration, store, ZEditorConstants.FONT_LATEX);
    fPreviewViewer.setEditable(false);

    String content = loadPreviewContentFromFile("ColorSettingPreviewCode.txt"); //$NON-NLS-1$
    IDocument document = new Document(content);
    CztUIPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
        document, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_LATEX);
    fPreviewViewer.setDocument(document);

    //    installSemanticHighlighting();

    return fPreviewViewer.getControl();
  }

  /*
   * Load the content of the previewed file
   */
  private String loadPreviewContentFromFile(String filename)
  {
    String line;
    String separator = System.getProperty("line.separator"); //$NON-NLS-1$
    StringBuffer buffer = new StringBuffer(512);
    BufferedReader reader = null;
    try {
      reader = new BufferedReader(new InputStreamReader(getClass()
          .getResourceAsStream(filename)));
      while ((line = reader.readLine()) != null) {
        buffer.append(line);
        buffer.append(separator);
      }
    } catch (IOException io) {
      //      CZTPlugin.log(io);
      io.printStackTrace();
    } finally {
      if (reader != null) {
        try {
          reader.close();
        } catch (IOException e) {
        }
      }
    }
    return buffer.toString();
  }

  /**
   * Returns the current highlighting color list item.
   * 
   * @return the current highlighting color list item
   * @since 3.0
   */
  private HighlightingColorListItem getHighlightingColorListItem()
  {
    IStructuredSelection selection = (IStructuredSelection) fListViewer
        .getSelection();
    Object element = selection.getFirstElement();
    if (element instanceof String)
      return null;
    return (HighlightingColorListItem) element;
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
  private void initializeDialogUnits(Control testControl)
  {
    // Compute and store a font metric
    GC gc = new GC(testControl);
    gc.setFont(JFaceResources.getDialogFont());
    fFontMetrics = gc.getFontMetrics();
    gc.dispose();
  }
}
