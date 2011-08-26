package net.sourceforge.czt.eclipse.views;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.IZPartitions;
import net.sourceforge.czt.eclipse.editors.ZSourceViewer;
import net.sourceforge.czt.eclipse.preferences.PreferenceConstants;
import net.sourceforge.czt.eclipse.preferences.SimpleZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.preferences.ZSourcePreviewerUpdater;
import net.sourceforge.czt.eclipse.util.IColorManager;
import net.sourceforge.czt.eclipse.util.IZFileType;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;

/**
 * @author Chengdong Xu
 */
public class ZConversionView extends ViewPart
{

  private final static String CONVERSION_NOT_AVAILABLE = "A conversion is not performed";

  private ZSourceViewer fSourceViewer;

  private IDocument fDocument;

  /**
   * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
   */
  @Override
  public void createPartControl(Composite parent)
  {
    IPreferenceStore generalTextStore = EditorsUI.getPreferenceStore();
    IPreferenceStore store = new ChainedPreferenceStore(new IPreferenceStore[]{
        CZTPlugin.getDefault().getPreferenceStore(), generalTextStore});

    fSourceViewer = new ZSourceViewer(parent, null, null, false, SWT.V_SCROLL | SWT.H_SCROLL, store);

    IColorManager colorManager = CZTPlugin.getDefault().getCZTTextTools().getColorManager();
    SimpleZSourceViewerConfiguration configuration = new SimpleZSourceViewerConfiguration(
        colorManager, store, null, IZPartitions.Z_PARTITIONING, false);
    fSourceViewer.configure(configuration);
//    Font font = JFaceResources.getFont(PreferenceConstants.EDITOR_TEXT_FONT);
    fSourceViewer.getTextWidget().setFont(JFaceResources.getTextFont());
    new ZSourcePreviewerUpdater(fSourceViewer, configuration, store);
//    FontData fontData = new FontData("CZT", 12, SWT.NORMAL);
//    fSourceViewer.getTextWidget().setFont(new Font(Display.getDefault(), fontData));
    fSourceViewer.setEditable(false);
    fDocument = new Document();
    fSourceViewer.setDocument(fDocument);

    initStatus();
  }

  /**
   * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
   */
  @Override
  public void setFocus()
  {
    fSourceViewer.getControl().setFocus();
  }

  public void setStatus(String fileName, String sourceMarkup,
      String targetMarkup)
  {
    if (fileName != null && fileName.trim() != null && sourceMarkup != null
        && sourceMarkup.trim() != null && targetMarkup != null
        && targetMarkup.trim() != null) {
      String information = "SOURCE:" + fileName + " -- " + "Original Markup:"
          + sourceMarkup + " -- " + "Target Markup:" + targetMarkup;
      setContentDescription(information);
    }
    else
      initStatus();
  }

  private void initStatus()
  {
    setContentDescription(CONVERSION_NOT_AVAILABLE);
  }

  public void setConversionData(String fileName, String sourceMarkup,
      String targetFileType, String data)
  {
//    fDocument.set(data);
    fDocument = new Document(data);
    if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(targetFileType)) {
      CZTPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
          fDocument, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_LATEX);
      setStatus(fileName, sourceMarkup, "LaTeX");
    }
    else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(targetFileType)) {
      CZTPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
          fDocument, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_UTF8);
      setStatus(fileName, sourceMarkup, "Unicode (encoded as UTF-8)");
    }
    else if (IZFileType.FILETYPE_UTF16.equalsIgnoreCase(targetFileType)) {
      CZTPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
          fDocument, IZPartitions.Z_PARTITIONING, IZFileType.FILETYPE_UTF16);
      setStatus(fileName, sourceMarkup, "Unicode (encoded as UTF-16)");
    }
    else {
      CZTPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
          fDocument, null);
      setStatus(fileName, sourceMarkup, targetFileType);
    }
    fSourceViewer.setDocument(fDocument);

  }
}
