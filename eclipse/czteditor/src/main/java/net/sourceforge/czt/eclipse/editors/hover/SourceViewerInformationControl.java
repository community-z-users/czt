/**
 * 
 */
package net.sourceforge.czt.eclipse.editors.hover;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.IZPartitions;
import net.sourceforge.czt.eclipse.editors.ZSourceViewer;
import net.sourceforge.czt.eclipse.preferences.SimpleZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.util.IZFileType;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IInformationControl;
import org.eclipse.jface.text.IInformationControlExtension;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.FocusListener;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;

/**
 * Source viewer based implementation of <code>IInformationControl</code>.
 * Displays information in a source viewer.
 * 
 * @author Chengdong Xu
 */
public class SourceViewerInformationControl
    implements
      IInformationControl,
      IInformationControlExtension,
      DisposeListener
{
  
  /** Border thickness in pixels. */
  private static final int BORDER= 1;
  /** The control's shell */
  private Shell fShell;
  /** The control's text widget */
  private StyledText fText;
  /** The control's source viewer */
  private SourceViewer fViewer;
  /** The optional status field. */
  private Label fStatusField;
  /** The separator for the optional status field. */
  private Label fSeparator;
  /** The font of the optional status text label. */
  private Font fStatusTextFont;
  /** The width size constraint. */
  private int fMaxWidth= SWT.DEFAULT;
  /** The height size constraint. */
  private int fMaxHeight= SWT.DEFAULT;

  
  /**
   * Creates a default information control with the given shell as parent. The given
   * information presenter is used to process the information to be displayed. The given
   * styles are applied to the created styled text widget.
   *
   * @param parent the parent shell
   * @param shellStyle the additional styles for the shell
   * @param style the additional styles for the styled text widget
   */
  public SourceViewerInformationControl(Shell parent, int shellStyle, int style) {
      this(parent, shellStyle, style, null);
  }
  
  /**
   * Creates a default information control with the given shell as parent. The given
   * information presenter is used to process the information to be displayed. The given
   * styles are applied to the created styled text widget.
   *
   * @param parent the parent shell
   * @param shellStyle the additional styles for the shell
   * @param style the additional styles for the styled text widget
   * @param statusFieldText the text to be used in the optional status field
   *                         or <code>null</code> if the status field should be hidden
   * @since 3.0
   */
  public SourceViewerInformationControl(Shell parent, int shellStyle, int style, String statusFieldText) {
      GridLayout layout;
      GridData gd;

      fShell= new Shell(parent, SWT.NO_FOCUS | SWT.ON_TOP | shellStyle);
      Display display= fShell.getDisplay();
      fShell.setBackground(display.getSystemColor(SWT.COLOR_BLACK));

      Composite composite= fShell;
      layout= new GridLayout(1, false);
      int border= ((shellStyle & SWT.NO_TRIM) == 0) ? 0 : BORDER;
      layout.marginHeight= border;
      layout.marginWidth= border;
      composite.setLayout(layout);
      gd= new GridData(GridData.FILL_HORIZONTAL);
      composite.setLayoutData(gd);

      if (statusFieldText != null) {
          composite= new Composite(composite, SWT.NONE);
          layout= new GridLayout(1, false);
          layout.marginHeight= 0;
          layout.marginWidth= 0;
          composite.setLayout(layout);
          gd= new GridData(GridData.FILL_BOTH);
          composite.setLayoutData(gd);
          composite.setForeground(display.getSystemColor(SWT.COLOR_INFO_FOREGROUND));
          composite.setBackground(display.getSystemColor(SWT.COLOR_INFO_BACKGROUND));
      }

      // Source viewer
      IPreferenceStore store= CZTPlugin.getDefault().getCombinedPreferenceStore();
      fViewer= new ZSourceViewer(composite, null, null, false, style, store);
      fViewer.configure(new SimpleZSourceViewerConfiguration(CZTPlugin.getDefault().getCZTTextTools().getColorManager(), store, null, IZPartitions.Z_PARTITIONING, false));
      fViewer.setEditable(false);

      fText= fViewer.getTextWidget();
      gd= new GridData(GridData.BEGINNING | GridData.FILL_BOTH);
      fText.setLayoutData(gd);
      fText.setForeground(parent.getDisplay().getSystemColor(SWT.COLOR_INFO_FOREGROUND));
      fText.setBackground(parent.getDisplay().getSystemColor(SWT.COLOR_INFO_BACKGROUND));
      
      initializeFont();

      fText.addKeyListener(new KeyListener() {

          public void keyPressed(KeyEvent e)  {
              if (e.character == 0x1B) // ESC
                  fShell.dispose();
          }

          public void keyReleased(KeyEvent e) {}
      });

      // Status field
      if (statusFieldText != null) {

          // Horizontal separator line
          fSeparator= new Label(composite, SWT.SEPARATOR | SWT.HORIZONTAL | SWT.LINE_DOT);
          fSeparator.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

          // Status field label
          fStatusField= new Label(composite, SWT.RIGHT);
          fStatusField.setText(statusFieldText);
          Font font= fStatusField.getFont();
          FontData[] fontDatas= font.getFontData();
          for (int i= 0; i < fontDatas.length; i++)
              fontDatas[i].setHeight(fontDatas[i].getHeight() * 9 / 10);
          fStatusTextFont= new Font(fStatusField.getDisplay(), fontDatas);
          fStatusField.setFont(fStatusTextFont);
          GridData gd2= new GridData(GridData.FILL_VERTICAL | GridData.FILL_HORIZONTAL | GridData.HORIZONTAL_ALIGN_BEGINNING | GridData.VERTICAL_ALIGN_BEGINNING);
          fStatusField.setLayoutData(gd2);

          // Regarding the color see bug 41128
          fStatusField.setForeground(display.getSystemColor(SWT.COLOR_WIDGET_DARK_SHADOW));

          fStatusField.setBackground(display.getSystemColor(SWT.COLOR_INFO_BACKGROUND));
      }

      addDisposeListener(this);
  }

  /**
   * Creates a default information control with the given shell as parent. The given
   * information presenter is used to process the information to be displayed. The given
   * styles are applied to the created styled text widget.
   *
   * @param parent the parent shell
   * @param style the additional styles for the styled text widget
   */
  public SourceViewerInformationControl(Shell parent,int style) {
      this(parent, SWT.NO_TRIM | SWT.TOOL, style);
  }

  /**
   * Creates a default information control with the given shell as parent. The given
   * information presenter is used to process the information to be displayed. The given
   * styles are applied to the created styled text widget.
   *
   * @param parent the parent shell
   * @param style the additional styles for the styled text widget
   * @param statusFieldText the text to be used in the optional status field
   *                         or <code>null</code> if the status field should be hidden
   * @since 3.0
   */
  public SourceViewerInformationControl(Shell parent,int style, String statusFieldText) {
      this(parent, SWT.NO_TRIM | SWT.TOOL, style, statusFieldText);
  }

  /**
   * Creates a default information control with the given shell as parent.
   * No information presenter is used to process the information
   * to be displayed. No additional styles are applied to the styled text widget.
   *
   * @param parent the parent shell
   */
  public SourceViewerInformationControl(Shell parent) {
      this(parent, SWT.NONE);
  }

  /**
   * Creates a default information control with the given shell as parent.
   * No information presenter is used to process the information
   * to be displayed. No additional styles are applied to the styled text widget.
   *
   * @param parent the parent shell
   * @param statusFieldText the text to be used in the optional status field
   *                         or <code>null</code> if the status field should be hidden
   * @since 3.0
   */
  public SourceViewerInformationControl(Shell parent, String statusFieldText) {
      this(parent, SWT.NONE, statusFieldText);
  }

  /**
   * Initialize the font to the CZT editor font.
   */
  private void initializeFont() {
      Font font= JFaceResources.getFont("org.eclipse.jdt.ui.editors.textfont"); //$NON-NLS-1$
      StyledText styledText= getViewer().getTextWidget();
      styledText.setFont(font);
  }

  /*
   * @see org.eclipse.jface.text.IInformationControlExtension2#setInput(java.lang.Object)
   */
  public void setInput(Object input) {
      if (input instanceof String)
          setInformation((String)input);
      else
          setInformation(null);
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#setInformation(java.lang.String)
   */
  public void setInformation(String information)
  {
    if (information == null) {
      fViewer.setInput(null);
      return;
  }

  IDocument doc= new Document(information);
  CZTPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(doc, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_UTF8);
  fViewer.setInput(doc);
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#setSize(int, int)
   */
  public void setSize(int width, int height) {

      if (fStatusField != null) {
          GridData gd= (GridData)fViewer.getTextWidget().getLayoutData();
          Point statusSize= fStatusField.computeSize(SWT.DEFAULT, SWT.DEFAULT, true);
          Point separatorSize= fSeparator.computeSize(SWT.DEFAULT, SWT.DEFAULT, true);
          gd.heightHint= height - statusSize.y - separatorSize.y;
      }
      fShell.setSize(width, height);

      if (fStatusField != null)
          fShell.pack(true);
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#setSizeConstraints(int, int)
   */
  public void setSizeConstraints(int maxWidth, int maxHeight) {
      fMaxWidth= maxWidth;
      fMaxHeight= maxHeight;
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#computeSizeHint()
   */
  public Point computeSizeHint() {
      // compute the preferred size
      int x= SWT.DEFAULT;
      int y= SWT.DEFAULT;
      Point size= fShell.computeSize(x, y);
      if (size.x > fMaxWidth)
          x= fMaxWidth;
      if (size.y > fMaxHeight)
          y= fMaxHeight;

      // recompute using the constraints if the preferred size is larger than the constraints
      if (x != SWT.DEFAULT || y != SWT.DEFAULT)
          size= fShell.computeSize(x, y, false);

      return size;
  }
  
  /*
   * @see org.eclipse.jface.text.IInformationControl#setLocation(org.eclipse.swt.graphics.Point)
   */
  public void setLocation(Point location) {
      fShell.setLocation(location);
  }
  
  /*
   * @see org.eclipse.jface.text.IInformationControl#addDisposeListener(org.eclipse.swt.events.DisposeListener)
   */
  public void addDisposeListener(DisposeListener listener) {
      fShell.addDisposeListener(listener);
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#removeDisposeListener(org.eclipse.swt.events.DisposeListener)
   */
  public void removeDisposeListener(DisposeListener listener) {
      fShell.removeDisposeListener(listener);
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#setForegroundColor(org.eclipse.swt.graphics.Color)
   */
  public void setForegroundColor(Color foreground) {
      fText.setForeground(foreground);
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#setBackgroundColor(org.eclipse.swt.graphics.Color)
   */
  public void setBackgroundColor(Color background) {
      fText.setBackground(background);
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#isFocusControl()
   */
  public boolean isFocusControl() {
      return fText.isFocusControl();
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#addFocusListener(org.eclipse.swt.events.FocusListener)
   */
  public void addFocusListener(FocusListener listener)
  {
    fText.addFocusListener(listener);
  }
  
  /*
   * @see org.eclipse.jface.text.IInformationControl#removeFocusListener(org.eclipse.swt.events.FocusListener)
   */
  public void removeFocusListener(FocusListener listener)
  {
    fText.removeFocusListener(listener);
  }

  /*
   * @see org.eclipse.jface.text.IInformationControl#setFocus()
   */
  public void setFocus()
  {
    fShell.forceFocus();
    fText.setFocus();
  }
  
  /*
   * @see @see org.eclipse.jface.text.IInformationControl#setVisible(boolean)
   */
  public void setVisible(boolean visible) {
    fShell.setVisible(visible);
  }
  
  /**
   * {@inheritDoc}
   * @see org.eclipse.jface.text.IInformationControl#dispose()
   */
  public final void dispose() {
      if (fShell != null && !fShell.isDisposed())
          fShell.dispose();
      else
          widgetDisposed(null);
  }
  
  /**
   * {@inheritDoc}
   * @see org.eclipse.swt.events.DisposeListener#widgetDisposed(org.eclipse.swt.events.DisposeEvent)
   */
  public void widgetDisposed(DisposeEvent event) {
      if (fStatusTextFont != null && !fStatusTextFont.isDisposed())
          fStatusTextFont.dispose();

      fStatusTextFont= null;
      fShell= null;
      fText= null;
  }

  /*
   * @see org.eclipse.jface.text.IInformationControlExtension#hasContents()
   */
  public boolean hasContents()
  {
    return fText.getCharCount() > 0;
  }
  
  protected ISourceViewer getViewer()  {
    return fViewer;
}
}
