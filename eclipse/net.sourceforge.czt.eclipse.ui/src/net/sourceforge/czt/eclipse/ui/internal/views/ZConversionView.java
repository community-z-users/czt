package net.sourceforge.czt.eclipse.ui.internal.views;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.internal.editors.FontUpdater;
import net.sourceforge.czt.eclipse.ui.internal.editors.ZSourceViewer;
import net.sourceforge.czt.eclipse.ui.internal.preferences.SimpleZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.ui.internal.util.IColorManager;
import net.sourceforge.czt.session.Markup;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;

/**
 * @author Chengdong Xu
 * @author Andrius Velykis
 */
public class ZConversionView extends ViewPart
{

  private final static String CONVERSION_NOT_AVAILABLE = "A conversion is not performed";

  private ZSourceViewer fSourceViewer;
  private FontUpdater fontUpdater;

  /**
   * @see org.eclipse.ui.part.WorkbenchPart#createPartControl(org.eclipse.swt.widgets.Composite)
   */
  @Override
  public void createPartControl(Composite parent)
  {
    IPreferenceStore generalTextStore = EditorsUI.getPreferenceStore();
    IPreferenceStore store = new ChainedPreferenceStore(new IPreferenceStore[]{
        CztUIPlugin.getDefault().getPreferenceStore(), generalTextStore});

    fSourceViewer = new ZSourceViewer(parent, null, null, false, SWT.V_SCROLL | SWT.H_SCROLL, store);

    IColorManager colorManager = CztUIPlugin.getDefault().getCZTTextTools().getColorManager();
    SimpleZSourceViewerConfiguration configuration = new SimpleZSourceViewerConfiguration(
        colorManager, store, null, IZPartitions.Z_PARTITIONING, false);
    fSourceViewer.configure(configuration);
    fontUpdater = FontUpdater.enableFor(fSourceViewer, configuration, store, JFaceResources.TEXT_FONT);
    fSourceViewer.setEditable(false);
    fSourceViewer.setDocument(new Document());

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
      String information = "File " + fileName + " converted to " + targetMarkup + " (originally " + sourceMarkup + ")";
      setContentDescription(information);
    }
    else
      initStatus();
  }

  private void initStatus()
  {
    setContentDescription(CONVERSION_NOT_AVAILABLE);
  }

  public void setConversionData(String fileName, Markup sourceMarkup,
      Markup targetMarkup, String data)
  {
    IDocument document = new Document(data);
    CztUIPlugin.getDefault().getCZTTextTools().setupCZTDocumentPartitioner(
        document, IZPartitions.Z_PARTITIONING, ZEditorUtil.getFileType(targetMarkup));
    
    setStatus(fileName, getMarkupLabel(sourceMarkup), getMarkupLabel(targetMarkup));
    
    fontUpdater.setFont(ZEditorUtil.getEditorFont(targetMarkup));
    fSourceViewer.setDocument(document);
  }
  
  private String getMarkupLabel(Markup markup) {
    if (markup == null) {
      return "<Unknown>";
    }
    
    switch (markup) {
      case LATEX: return "LaTeX";
      case UNICODE: return "Unicode";
      case ZML: return "XML";
      default: return markup.toString();
    }
  }
}
