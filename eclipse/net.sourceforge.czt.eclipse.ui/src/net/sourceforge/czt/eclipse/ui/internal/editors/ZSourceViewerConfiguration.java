/**
 * Created on 2005-10-17
 */

package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;
import net.sourceforge.czt.eclipse.ui.internal.editors.hover.ZAnnotationHover;
import net.sourceforge.czt.eclipse.ui.internal.editors.hover.ZTextHover;
import net.sourceforge.czt.eclipse.ui.internal.editors.latex.ZCharCodeScanner;
import net.sourceforge.czt.eclipse.ui.internal.editors.latex.ZLatexCodeScanner;
import net.sourceforge.czt.eclipse.ui.internal.editors.latex.ZLatexDoubleClickStrategy;
import net.sourceforge.czt.eclipse.ui.internal.editors.latex.ZLatexPartitionScanner;
import net.sourceforge.czt.eclipse.ui.internal.editors.unicode.ZUnicodeCodeScanner;
import net.sourceforge.czt.eclipse.ui.internal.editors.unicode.ZUnicodeDoubleClickStrategy;
import net.sourceforge.czt.eclipse.ui.internal.editors.unicode.ZUnicodePartitionScanner;
import net.sourceforge.czt.eclipse.ui.internal.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.ui.internal.util.IColorManager;
import net.sourceforge.czt.eclipse.ui.internal.util.IZColorConstants;
import net.sourceforge.czt.eclipse.ui.internal.util.IZFileType;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextViewerExtension2;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.IContentAssistant;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.reconciler.IReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.rules.RuleBasedScanner;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.editors.text.TextSourceViewerConfiguration;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * 
 * @author Chengdong Xu
 *
 */
public class ZSourceViewerConfiguration extends TextSourceViewerConfiguration
{

  private CZTTextTools fCZTTextTools;

  private ZEditor fTextEditor;

  private IColorManager fColorManager;

  private AbstractZCodeScanner fCodeScanner;

  private AbstractZCodeScanner fNarrativeCodeScanner;

  private AbstractZCodeScanner fZCharScanner;

  private IPreferenceStore fPreferenceStore;

  /**
   * The document partitioning
   */
  private String fDocumentPartitioning;

  /**
   * Creates a new Z source viewer configuration for viewers in the given fEditor
   * using the given preference store, the color manager and the specified document partitioning.
   * <p>
   * Creates a Z source viewer configuration in the new setup without text tools. Clients are
   * allowed to call {@link ZSourceViewerConfiguration#handlePropertyChangeEvent(PropertyChangeEvent)}
   * and disallowed to call {@link ZSourceViewerConfiguration#getPreferenceStore()} on the resulting
   * Z source viewer configuration.
   * </p>
   *
   * @param colorManager the color manager
   * @param preferenceStore the preference store, can be read-only
   * @param fEditor the fEditor in which the configured viewer(s) will reside, or <code>null</code> if none
   * @param partitioning the document partitioning for this configuration, or <code>null</code> for the default partitioning
   */
  public ZSourceViewerConfiguration(IColorManager colorManager,
      IPreferenceStore preferenceStore, ZEditor editor, String partitioning)
  {
    super(preferenceStore);
    fColorManager = colorManager;
    fTextEditor = editor;
    fDocumentPartitioning = partitioning;
    fPreferenceStore = preferenceStore;
    initializeScanners();
    //    System.out.println("ZSourceViewerConfiguration constructor");
  }

  /*
   * Initialize the scanners
   */
  private void initializeScanners()
  {
    fNarrativeCodeScanner = new ZCommentScanner(getColorManager(),
        fPreferenceStore, IZColorConstants.CZT_NARRATIVE);
    fZCharScanner = new ZCharCodeScanner(getColorManager(), fPreferenceStore);
  }

  /**
   * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getConfiguredDocumentPartitioning(org.eclipse.jface.text.source.ISourceViewer)
   */
  public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer)
  {
    //    System.out
    //        .println("ZSourceViewerConfiguration.getConfiguredDocumentPartitioning");
    if (fDocumentPartitioning != null)
      return fDocumentPartitioning;

    return super.getConfiguredDocumentPartitioning(sourceViewer);
  }

  /**
   * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getConfiguredContentTypes(org.eclipse.jface.text.source.ISourceViewer)
   */
  public String[] getConfiguredContentTypes(ISourceViewer sourceViewer)
  {
    //    System.out.println("ZSourceViewerConfiguration.getConfiguredContentTypes");
    String sourceFileType = getSourceFileType();

    List<String> contentTypes = new ArrayList<String>();
    contentTypes.add(IDocument.DEFAULT_CONTENT_TYPE);

    if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(sourceFileType)) {
      for (int i = 0; i < ZLatexPartitionScanner.Z_PARTITION_TYPES_LATEX.length; i++) {
        contentTypes.add(ZLatexPartitionScanner.Z_PARTITION_TYPES_LATEX[i]);
      }
    }
    else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(sourceFileType)
        || IZFileType.FILETYPE_UTF16.equalsIgnoreCase(sourceFileType)) {
      for (int i = 0; i < ZUnicodePartitionScanner.Z_PARTITION_TYPES_UNICODE.length; i++) {
        contentTypes.add(ZUnicodePartitionScanner.Z_PARTITION_TYPES_UNICODE[i]);
      }
    }

    String[] types = new String[contentTypes.size()];
    contentTypes.toArray(types);

    return types;
  }

  /**
   * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getDefaultPrefixes(org.eclipse.jface.text.source.ISourceViewer, java.lang.String)
   */
  public String getDefaultPrefix(ISourceViewer sourceViewer, String contentType)
  {
    //    System.out.println("ZSourceViewerConfiguration.getDefaultPrefix");
    super.getDefaultPrefixes(sourceViewer, contentType);
    return (IDocument.DEFAULT_CONTENT_TYPE.equals(contentType) ? "//" : null); //$NON-NLS-1$
  }

  /**
   * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getDoubleClickStrategy(org.eclipse.jface.text.source.ISourceViewer, java.lang.String)
   */
  public ITextDoubleClickStrategy getDoubleClickStrategy(
      ISourceViewer sourceViewer, String contentType)
  {
    String sourceFileType = getSourceFileType();

    if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(sourceFileType))
      return new ZLatexDoubleClickStrategy();
    else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(sourceFileType)
        || IZFileType.FILETYPE_UTF16.equalsIgnoreCase(sourceFileType))
      return new ZUnicodeDoubleClickStrategy();
    else
      return super.getDoubleClickStrategy(sourceViewer, contentType);
  }

  @Override
  public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer)
  {
    return new ZAnnotationHover()
    {
      protected boolean isIncluded(Annotation annotation)
      {
        return super.isIncluded(annotation)
            && isShowInVerticalRuler(annotation);
      }
    };
  }

  @Override
  public IAnnotationHover getOverviewRulerAnnotationHover(
      ISourceViewer sourceViewer)
  {
    return new ZAnnotationHover(true)
    {
      protected boolean isIncluded(Annotation annotation)
      {
        return super.isIncluded(annotation)
            && isShowInOverviewRuler(annotation);
      }
    };
  }

/*
   * @see SourceViewerConfiguration#getConfiguredTextHoverStateMasks(ISourceViewer, String)
   * @since 2.1
   */
  //  public int[] getConfiguredTextHoverStateMasks(ISourceViewer sourceViewer, String contentType) {
  //      JavaEditorTextHoverDescriptor[] hoverDescs= JavaPlugin.getDefault().getJavaEditorTextHoverDescriptors();
  //      int stateMasks[]= new int[hoverDescs.length];
  //      int stateMasksLength= 0;
  //      for (int i= 0; i < hoverDescs.length; i++) {
  //          if (hoverDescs[i].isEnabled()) {
  //              int j= 0;
  //              int stateMask= hoverDescs[i].getStateMask();
  //              while (j < stateMasksLength) {
  //                  if (stateMasks[j] == stateMask)
  //                      break;
  //                  j++;
  //              }
  //              if (j == stateMasksLength)
  //                  stateMasks[stateMasksLength++]= stateMask;
  //          }
  //      }
  //      if (stateMasksLength == hoverDescs.length)
  //          return stateMasks;
  //
  //      int[] shortenedStateMasks= new int[stateMasksLength];
  //      System.arraycopy(stateMasks, 0, shortenedStateMasks, 0, stateMasksLength);
  //      return shortenedStateMasks;
  //  }
  /*
   * @see SourceViewerConfiguration#getTextHover(ISourceViewer, String, int)
   * @since 2.1
   */
  public ITextHover getTextHover(ISourceViewer sourceViewer,
      String contentType, int stateMask)
  {
    //      JavaEditorTextHoverDescriptor[] hoverDescs= JavaPlugin.getDefault().getJavaEditorTextHoverDescriptors();
    //      int i= 0;
    //      while (i < hoverDescs.length) {
    //          if (hoverDescs[i].isEnabled() &&  hoverDescs[i].getStateMask() == stateMask)
    //              return new JavaEditorTextHoverProxy(hoverDescs[i], getEditor());
    //          i++;
    //      }

    //      return null;
    //return new ZTextHover(sourceViewer, contentType, getEditor());
    return new ZTextHover(sourceViewer, getEditor());
  }

  /**
   * @see SourceViewerConfiguration#getTextHover(ISourceViewer, String)
   */
  public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType)
  {
    return getTextHover(sourceViewer, contentType,
        ITextViewerExtension2.DEFAULT_HOVER_STATE_MASK);
  }

  /**
   * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getPresentationReconciler(org.eclipse.jface.text.source.ISourceViewer)
   */
  public IPresentationReconciler getPresentationReconciler(
      ISourceViewer sourceViewer)
  {
    //    System.out
    //        .println("ZSourceViewerConfiguration.getPresentationReconciler starts");
    PresentationReconciler reconciler = new PresentationReconciler();
    reconciler
        .setDocumentPartitioning(getConfiguredDocumentPartitioning(sourceViewer));

    String sourceFileType = getSourceFileType();
    //    System.out.println("SourceFileType: " + sourceFileType);
    DefaultDamagerRepairer dr;
    if ((sourceFileType == null) || sourceFileType.equals("")) {
      //      System.out.println("null file type");
    }
    else if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(sourceFileType)) {
      dr = new DefaultDamagerRepairer(getZCharScanner());
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_LATEX_ZCHAR);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_LATEX_ZCHAR);

      dr = new DefaultDamagerRepairer(getCodeScanner());
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_LATEX_ZED);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_LATEX_ZED);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_LATEX_AXDEF);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_LATEX_AXDEF);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_LATEX_GENAX);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_LATEX_GENAX);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_LATEX_THEOREM);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_LATEX_THEOREM);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_LATEX_PROOFSCRIPT);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_LATEX_PROOFSCRIPT);
    }
    else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(sourceFileType)
        || IZFileType.FILETYPE_UTF16.equalsIgnoreCase(sourceFileType)) {
      dr = new DefaultDamagerRepairer(getCodeScanner());
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_UNICODE_ZSECTION);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_UNICODE_ZSECTION);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_UNICODE_GENAX);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_UNICODE_GENAX);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH);
      reconciler.setDamager(dr, IZPartitions.Z_PARAGRAPH_UNICODE_PROOFSCRIPT);
      reconciler.setRepairer(dr, IZPartitions.Z_PARAGRAPH_UNICODE_PROOFSCRIPT);
    }

    //Set the DamagerRepairer to default content type
    dr = new DefaultDamagerRepairer(getNarrativeCodeScanner());
    reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
    reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
    //    System.out
    //        .println("ZSourceViewerConfiguration.getPresentationReconciler finishes");
    return reconciler;
  }

  /*
   * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getContentAssistant(org.eclipse.jface.text.source.ISourceViewer)
   */
  public IContentAssistant getContentAssistant(ISourceViewer sourceViewer)
  {
    ContentAssistant assistant = new ContentAssistant();
    assistant.setContentAssistProcessor(new ZCompletionProcessor(fTextEditor), IDocument.DEFAULT_CONTENT_TYPE);
    assistant.enableAutoActivation(true);
    assistant.setInformationControlCreator(getInformationControlCreator(sourceViewer));
    return assistant;
  }

  /**
   * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getReconciler(ISourceViewer)
   */

  public IReconciler getReconciler(ISourceViewer sourceViewer)
  {
    //    System.out.println("ZSourceViewerConfiguration.getReconciler starts");
    final ITextEditor editor = getEditor();

    if (editor != null && editor.isEditable()) {
      CZTCompositeReconcilingStrategy strategy = new CZTCompositeReconcilingStrategy(
          editor, getConfiguredDocumentPartitioning(sourceViewer));
      ZReconciler reconciler = new ZReconciler(editor, strategy, false);
      reconciler.setIsIncrementalReconciler(false);
      reconciler.setProgressMonitor(new NullProgressMonitor());
      reconciler.setDelay(500);
      //      System.out.println("ZSourceViewerConfiguration.getReconciler finishes");
      return reconciler;
    }

    //    System.out.println("ZSourceViewerConfiguration.getReconciler finishes");

    return null;
  }

  /**
   * Returns the fEditor in which the configured viewer(s) will reside.
   *
   * @return the enclosing fEditor
   */
  protected ITextEditor getEditor()
  {
    return fTextEditor;
  }

  public String getSourceFileType()
  {
    //    System.out.println("ZSourceViewerConfiguration.getSourceFileType");
    ITextEditor editor = getEditor();
    if ((editor != null) && (editor instanceof ZEditor))
      return ((ZEditor) editor).getFileType();

    return null;
  }

  /**
   * Returns the color manager for this configuration.
   *
   * @return the color manager
   */
  protected IColorManager getColorManager()
  {
    return fColorManager;
  }

  protected RuleBasedScanner getCodeScanner()
  {
    if (fCodeScanner == null) {
      String fileType = getSourceFileType();
      if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(fileType))
        fCodeScanner = new ZLatexCodeScanner(getColorManager(),
            fPreferenceStore);
      else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(fileType)
          || IZFileType.FILETYPE_UTF16.equalsIgnoreCase(fileType))
        fCodeScanner = new ZUnicodeCodeScanner(getColorManager(),
            fPreferenceStore);
      else
        fCodeScanner = null;
    }

    return fCodeScanner;
  }

  protected RuleBasedScanner getNarrativeCodeScanner()
  {
    if (fNarrativeCodeScanner == null)
      fNarrativeCodeScanner = new ZCommentScanner(getColorManager(),
          fPreferenceStore, IZColorConstants.CZT_NARRATIVE);

    return fNarrativeCodeScanner;
  }

  protected RuleBasedScanner getZCharScanner()
  {
    if (fZCharScanner == null)
      fZCharScanner = new ZCharCodeScanner(getColorManager(), fPreferenceStore);
    return fZCharScanner;
  }

  /**
   * @return <code>true</code> iff the new setup without text tools is in use.
   *
   * @since 3.0
   */
  private boolean isNewSetup()
  {
    return fCZTTextTools == null;
  }

  /**
   * Determines whether the preference change encoded by the given event
   * changes the behavior of one of its contained components.
   *
   * @param event the event to be investigated
   * @return <code>true</code> if event causes a behavioral change
   * @since 3.0
   */
  public boolean affectsTextPresentation(PropertyChangeEvent event)
  {
    return fCodeScanner.affectsBehavior(event)
        || fZCharScanner.affectsBehavior(event)
        || fNarrativeCodeScanner.affectsBehavior(event);
  }

  /**
   * Adapts the behavior of the contained components to the change
   * encoded in the given event.
   * <p>
   * Clients are not allowed to call this method if the old setup with
   * text tools is in use.
   * </p>
   *
   * @param event the event to which to adapt
   * @see ZSourceViewerConfiguration#ZSourceViewerConfiguration(IColorManager, IPreferenceStore, ITextEditor, String)
   * @since 3.0
   */
  public void handlePropertyChangeEvent(PropertyChangeEvent event)
  {
    Assert.isTrue(isNewSetup());
    if (fCodeScanner.affectsBehavior(event))
      fCodeScanner.adaptToPreferenceChange(event);
    if (fZCharScanner.affectsBehavior(event))
      fZCharScanner.adaptToPreferenceChange(event);
    if (fNarrativeCodeScanner.affectsBehavior(event))
      fNarrativeCodeScanner.adaptToPreferenceChange(event);
    //        if (fJavaDoubleClickSelector != null && JavaCore.COMPILER_SOURCE.equals(event.getProperty()))
    //            if (event.getNewValue() instanceof String)
    //                fJavaDoubleClickSelector.setSourceVersion((String) event.getNewValue());
  }

}
