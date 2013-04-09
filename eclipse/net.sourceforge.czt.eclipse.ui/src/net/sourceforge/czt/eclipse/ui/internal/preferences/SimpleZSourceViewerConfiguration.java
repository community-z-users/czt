/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import net.sourceforge.czt.eclipse.ui.internal.editors.ZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.util.IColorManager;
import net.sourceforge.czt.eclipse.ui.internal.util.IZFileType;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IAutoEditStrategy;
import org.eclipse.jface.text.IInformationControlCreator;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.contentassist.IContentAssistant;
import org.eclipse.jface.text.formatter.IContentFormatter;
import org.eclipse.jface.text.hyperlink.IHyperlinkDetector;
import org.eclipse.jface.text.information.IInformationPresenter;
import org.eclipse.jface.text.reconciler.IReconciler;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;

/**
 * A simple {@linkplain net.sourceforge.czt.eclipse.ui.internal.editors.ZSourceViewerConfiguration Z source viewer configuration}.
 * <p>
 * This simple source viewer configuration basically provides syntax coloring
 * and disables all other features like code assist, quick outlines, hyperlinking, etc.
 * </p>
 * 
 * @author Chengdong Xu
 */
public class SimpleZSourceViewerConfiguration
    extends
      ZSourceViewerConfiguration
{

  private boolean fConfigureFormatter;

  /**
   * Creates a new Z source viewer configuration for viewers in the given fEditor
   * using the given preference store, the color manager and the specified document partitioning.
   *
   * @param colorManager the color manager
   * @param preferenceStore the preference store, can be read-only
   * @param fEditor the fEditor in which the configured viewer(s) will reside, or <code>null</code> if none
   * @param partitioning the document partitioning for this configuration, or <code>null</code> for the default partitioning
   * @param configureFormatter <code>true</code> if a content formatter should be configured
   */
  public SimpleZSourceViewerConfiguration(IColorManager colorManager,
      IPreferenceStore preferenceStore, ZEditor editor,
      String partitioning, boolean configureFormatter)
  {
    super(colorManager, preferenceStore, editor, partitioning);
  }

  /*
   * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getAutoEditStrategies(org.eclipse.jface.text.source.ISourceViewer, java.lang.String)
   */
  public IAutoEditStrategy[] getAutoEditStrategies(ISourceViewer sourceViewer,
      String contentType)
  {
    return null;
  }

  /*
   * @see SourceViewerConfiguration#getAnnotationHover(ISourceViewer)
   */
  public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer)
  {
    return null;
  }

  /*
   * @see SourceViewerConfiguration#getOverviewRulerAnnotationHover(ISourceViewer)
   */
  public IAnnotationHover getOverviewRulerAnnotationHover(
      ISourceViewer sourceViewer)
  {
    return null;
  }

  /*
   * @see SourceViewerConfiguration#getConfiguredTextHoverStateMasks(ISourceViewer, String)
   */
  public int[] getConfiguredTextHoverStateMasks(ISourceViewer sourceViewer,
      String contentType)
  {
    return null;
  }

  /*
   * @see SourceViewerConfiguration#getTextHover(ISourceViewer, String, int)
   */
  public ITextHover getTextHover(ISourceViewer sourceViewer,
      String contentType, int stateMask)
  {
    return null;
  }

  /*
   * @see SourceViewerConfiguration#getTextHover(ISourceViewer, String)
   */
  public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType)
  {
    return null;
  }

  /*
   * @see SourceViewerConfiguration#getContentFormatter(ISourceViewer)
   */
  public IContentFormatter getContentFormatter(ISourceViewer sourceViewer)
  {
    if (fConfigureFormatter)
      return super.getContentFormatter(sourceViewer);
    else
      return null;
  }

  /*
   * @see SourceViewerConfiguration#getInformationControlCreator(ISourceViewer)
   */
  public IInformationControlCreator getInformationControlCreator(
      ISourceViewer sourceViewer)
  {
    return null;
  }

  /**
   * @see SourceViewerConfiguration#getInformationPresenter(ISourceViewer)
   */
  public IInformationPresenter getInformationPresenter(
      ISourceViewer sourceViewer)
  {
    return null;
  }

  /*
   * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getHyperlinkDetectors(org.eclipse.jface.text.source.ISourceViewer)
   */
  public IHyperlinkDetector[] getHyperlinkDetectors(ISourceViewer sourceViewer)
  {
    return null;
  }

  public IContentAssistant getContentAssistant(ISourceViewer sourceViewer)
  {
    return null;
  }

  public IReconciler getReconciler(ISourceViewer sourceViewer)
  {
    return null;
  }

  /**
   * @see net.sourceforge.czt.eclipse.ui.internal.editors.ZSourceViewerConfiguration#getSourceFileType()
   */
  public String getSourceFileType()
  {
    return IZFileType.FILETYPE_LATEX;
  }
}
