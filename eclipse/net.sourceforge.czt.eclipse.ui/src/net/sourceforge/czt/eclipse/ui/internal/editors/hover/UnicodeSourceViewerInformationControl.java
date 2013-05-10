/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.internal.editors.hover;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.internal.util.IZFileType;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

/**
 * @author Chengdong
 *
 */
public class UnicodeSourceViewerInformationControl
    extends
      SourceViewerInformationControl
{

  /**
   * @param parent
   * @param shellStyle
   * @param style
   */
  public UnicodeSourceViewerInformationControl(Shell parent, int shellStyle,
      int style)
  {
    super(parent, shellStyle, style);
    // TODO Auto-generated constructor stub
  }

  /**
   * @param parent
   * @param shellStyle
   * @param style
   * @param statusFieldText
   */
  public UnicodeSourceViewerInformationControl(Shell parent, int shellStyle,
      int style, String statusFieldText)
  {
    super(parent, shellStyle, style, statusFieldText);
    // TODO Auto-generated constructor stub
  }

  /**
   * @param parent
   * @param style
   */
  public UnicodeSourceViewerInformationControl(Shell parent, int style)
  {
    super(parent, style);
    // TODO Auto-generated constructor stub
  }

  /**
   * @param parent
   * @param style
   * @param statusFieldText
   */
  public UnicodeSourceViewerInformationControl(Shell parent, int style,
      String statusFieldText)
  {
    super(parent, style, statusFieldText);
    // TODO Auto-generated constructor stub
  }

  /**
   * @param parent
   */
  public UnicodeSourceViewerInformationControl(Shell parent)
  {
    super(parent);
    // TODO Auto-generated constructor stub
  }

  /**
   * @param parent
   * @param statusFieldText
   */
  public UnicodeSourceViewerInformationControl(Shell parent,
      String statusFieldText)
  {
    super(parent, statusFieldText);
    // TODO Auto-generated constructor stub
  }
  
  /**
   * Initialize the font to the CZT editor font.
   */
  protected void initializeFont() {
    FontData viewFontData = new FontData();
    viewFontData.setName("CZT"); //$NON-NLS-1$
    //        viewFontData.setHeight(10);
    //        viewFontData.setStyle(SWT.BOLD);
    Font cztUnicodeFont = new Font(Display.getDefault(), viewFontData);
    StyledText styledText= getViewer().getTextWidget();
    styledText.setFont(cztUnicodeFont);
  }
  // TODO: never used? private->protected
  
  /*
   * @see org.eclipse.jface.text.IInformationControl#setInformation(java.lang.String)
   */
  public void setInformation(String information)
  {
    if (information == null) {
      ((SourceViewer)getViewer()).setInput(null);
      return;
    }

    IDocument doc= new Document(information);
    CztUIPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(doc, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_UTF8);
    ((SourceViewer)getViewer()).setInput(doc);
  }
}
