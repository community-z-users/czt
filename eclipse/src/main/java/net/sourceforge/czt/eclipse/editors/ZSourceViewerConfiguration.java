/**
 * Created on 2005-10-17
 */
package net.sourceforge.czt.eclipse.editors;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.latex.ZLatexDoubleClickStrategy;
import net.sourceforge.czt.eclipse.editors.latex.ZLatexPartitionScanner;
import net.sourceforge.czt.eclipse.editors.unicode.ZUnicodeDoubleClickStrategy;
import net.sourceforge.czt.eclipse.editors.unicode.ZUnicodePartitionScanner;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.util.CZTColorManager;
import net.sourceforge.czt.eclipse.util.IZColorConstants;
import net.sourceforge.czt.eclipse.util.IZFileType;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.IContentAssistant;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.reconciler.IReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * 
 * @author Chengdong Xu
 *
 */
public class ZSourceViewerConfiguration
	extends AbstractZSourceViewerConfiguration {
	
	/**
	 * The constructor
	 * @param editor
	 */
	public ZSourceViewerConfiguration(ITextEditor editor) {
		super(editor);
		System.out.println("ZSourceViewerConfiguration constructor");
	}
	
	/*
	 * @see org.eclipse.jface.text.source.SourceViewerConfiguration#getConfiguredDocumentPartitioning(org.eclipse.jface.text.source.ISourceViewer)
	 */
	public String getConfiguredDocumentPartitioning(ISourceViewer sourceViewer) {
		System.out.println("ZSourceViewerConfiguration.getConfiguredDocumentPartitioning");
		return CZTPlugin.Z_PARTITIONING;
	}
	
	
	/* (non-Javadoc)
	 * Method declared on SourceViewerConfiguration
	 */
	public String[] getConfiguredContentTypes(ISourceViewer sourceViewer) {
		System.out.println("ZSourceViewerConfiguration.getConfiguredContentTypes");
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
	
	/* (non-Javadoc)
	 * Method declared on SourceViewerConfiguration
	 */
	public String getDefaultPrefix(ISourceViewer sourceViewer, String contentType) {
		System.out.println("ZSourceViewerConfiguration.getDefaultPrefix");
		return (IDocument.DEFAULT_CONTENT_TYPE.equals(contentType) ? "//" : null); //$NON-NLS-1$
	}
	
	/**
	 * Method declared on SourceViewerConfiguration
	 * @see org.eclipse.jface.text.source.SourceViewerConfiguration
	 */
	public ITextDoubleClickStrategy getDoubleClickStrategy(ISourceViewer sourceViewer, String contentType) {
		System.out.println("ZSourceViewerConfiguration.getDoubleClickStrategy");
		String sourceFileType = getSourceFileType();
		
		if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(sourceFileType))
			return new ZLatexDoubleClickStrategy();
		else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(sourceFileType)
				|| IZFileType.FILETYPE_UTF16.equalsIgnoreCase(sourceFileType))
			return new ZUnicodeDoubleClickStrategy();
		else
			return super.getDoubleClickStrategy(sourceViewer, contentType);
	}
	
	/**
	 * Define reconciler for MyEditor
	 */
	public IPresentationReconciler getPresentationReconciler(
			ISourceViewer sourceViewer) {
		System.out.println("ZSourceViewerConfiguration.getPresentationReconciler starts");
		CZTColorManager colorManager = CZTPlugin.getDefault().getCZTColorManager();
		PresentationReconciler reconciler= new PresentationReconciler();
		reconciler.setDocumentPartitioning(
			getConfiguredDocumentPartitioning(sourceViewer));
		
		String sourceFileType = getSourceFileType();
		System.out.println("SourceFileType: " + sourceFileType);
		DefaultDamagerRepairer dr;
		if ((sourceFileType == null) || sourceFileType.equals("")) {
			System.out.println("null file type");
		}
		else if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(sourceFileType)) {
			for (int i = 0; i < ZLatexPartitionScanner.Z_PARTITION_TYPES_LATEX.length; i++) {
				
				dr = new DefaultDamagerRepairer(
						CZTPlugin.getDefault().getZLatexCodeScanner());
				reconciler.setDamager(dr, ZLatexPartitionScanner.Z_PARTITION_TYPES_LATEX[i]);
				reconciler.setRepairer(dr, ZLatexPartitionScanner.Z_PARTITION_TYPES_LATEX[i]);
			}
		}
		else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(sourceFileType)
				|| IZFileType.FILETYPE_UTF16.equalsIgnoreCase(sourceFileType)) {
			for (int i = 0; i < ZUnicodePartitionScanner.Z_PARTITION_TYPES_UNICODE.length; i++) {
				dr = new DefaultDamagerRepairer(
						CZTPlugin.getDefault().getZUnicodeCodeScanner());
				reconciler.setDamager(dr, ZUnicodePartitionScanner.Z_PARTITION_TYPES_UNICODE[i]);
				reconciler.setRepairer(dr, ZUnicodePartitionScanner.Z_PARTITION_TYPES_UNICODE[i]);
			}
		}
		
		//Set the DamagerRepairer to default content type
		dr= new DefaultDamagerRepairer(new SingleTokenScanner(
				new TextAttribute(colorManager.getColor(IZColorConstants.MULTI_LINE_COMMENT))));
		reconciler.setDamager(dr, IDocument.DEFAULT_CONTENT_TYPE);
		reconciler.setRepairer(dr, IDocument.DEFAULT_CONTENT_TYPE);
		System.out.println("ZSourceViewerConfiguration.getPresentationReconciler finishes");
		return reconciler;
	}
	
	public IContentAssistant getContentAssistant(ISourceViewer sourceViewer) {
		System.out.println("ZSourceViewerConfiguration.getContentAssistant starts");
		ContentAssistant assistant = new ContentAssistant();
		assistant.setContentAssistProcessor(
			new ZCompletionProcessor(),
			IDocument.DEFAULT_CONTENT_TYPE);
		assistant.enableAutoActivation(true);
		assistant.setAutoActivationDelay(500);
		assistant.setProposalPopupOrientation(
			IContentAssistant.PROPOSAL_OVERLAY);
		System.out.println("ZSourceViewerConfiguration.getContentAssistant finishes");
		return assistant;
	}
	
	/*
	 * @see SourceViewerConfiguration#getReconciler(ISourceViewer)
	 */
	
	public IReconciler getReconciler(ISourceViewer sourceViewer) {
		System.out.println("ZSourceViewerConfiguration.getReconciler starts");
		final ITextEditor editor= getEditor();
		
		if (editor != null && editor.isEditable()) {
			ZReconcilingStrategy strategy= new ZReconcilingStrategy();
			ZReconciler reconciler= new ZReconciler(editor, strategy, false);
			reconciler.setIsIncrementalReconciler(false);
			reconciler.setProgressMonitor(new NullProgressMonitor());
			reconciler.setDelay(500);
			System.out.println("ZSourceViewerConfiguration.getReconciler finishes");
			return reconciler;
		}
		
		System.out.println("ZSourceViewerConfiguration.getReconciler finishes");
		
		return null;
	}
	
	public String getSourceFileType() {
		System.out.println("ZSourceViewerConfiguration.getSourceFileType");
		ITextEditor editor = getEditor();
		if (editor instanceof ZEditor)
			return ((ZEditor) editor).getFileType();
		
		return null;
	}
}
