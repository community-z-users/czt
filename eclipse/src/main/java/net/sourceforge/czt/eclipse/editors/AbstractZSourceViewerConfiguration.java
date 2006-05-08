/**
 * 
 */
package net.sourceforge.czt.eclipse.editors;

import net.sourceforge.czt.eclipse.editors.hover.ZAnnotationHover;
import net.sourceforge.czt.eclipse.editors.hover.ZTextHover;

import org.eclipse.jface.text.ITextHover;
import org.eclipse.jface.text.ITextViewerExtension2;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.rules.BufferedRuleBasedScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.source.IAnnotationHover;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.ui.texteditor.ITextEditor;

/**
 * @author Chengdong Xu
 *
 */
public abstract class AbstractZSourceViewerConfiguration
	extends SourceViewerConfiguration {
	
	private ITextEditor fTextEditor;
	
	/**
	 * Single token scanner.
	 */
	static class SingleTokenScanner extends BufferedRuleBasedScanner {
		public SingleTokenScanner(TextAttribute attribute) {
			setDefaultReturnToken(new Token(attribute));
		}
	}
	
	public AbstractZSourceViewerConfiguration(ITextEditor editor) {
		super();
		fTextEditor = editor;
	}
	

	/**
	 * Returns the editor in which the configured viewer(s) will reside.
	 *
	 * @return the enclosing editor
	 */
	protected ITextEditor getEditor() {
		return fTextEditor;
	}
	
	/**
	 * Sets the editor in which the configured viewer(s) will reside.
	 */
	protected void setEditor(ITextEditor editor) {
		fTextEditor = editor;
	}
	
	/*
	 * @see SourceViewerConfiguration#getAnnotationHover(ISourceViewer)
	 */
	public IAnnotationHover getAnnotationHover(ISourceViewer sourceViewer) {
		return new ZAnnotationHover(ZAnnotationHover.VERTICAL_RULER_HOVER);
	}

	/*
	 * @see SourceViewerConfiguration#getOverviewRulerAnnotationHover(ISourceViewer)
	 * @since 3.0
	 */
	public IAnnotationHover getOverviewRulerAnnotationHover(ISourceViewer sourceViewer) {
		return new ZAnnotationHover(ZAnnotationHover.OVERVIEW_RULER_HOVER);
	}
	
	/*
	 * @see SourceViewerConfiguration#getConfiguredTextHoverStateMasks(ISourceViewer, String)
	 * @since 2.1
	 */
//	public int[] getConfiguredTextHoverStateMasks(ISourceViewer sourceViewer, String contentType) {
//		JavaEditorTextHoverDescriptor[] hoverDescs= JavaPlugin.getDefault().getJavaEditorTextHoverDescriptors();
//		int stateMasks[]= new int[hoverDescs.length];
//		int stateMasksLength= 0;
//		for (int i= 0; i < hoverDescs.length; i++) {
//			if (hoverDescs[i].isEnabled()) {
//				int j= 0;
//				int stateMask= hoverDescs[i].getStateMask();
//				while (j < stateMasksLength) {
//					if (stateMasks[j] == stateMask)
//						break;
//					j++;
//				}
//				if (j == stateMasksLength)
//					stateMasks[stateMasksLength++]= stateMask;
//			}
//		}
//		if (stateMasksLength == hoverDescs.length)
//			return stateMasks;
//
//		int[] shortenedStateMasks= new int[stateMasksLength];
//		System.arraycopy(stateMasks, 0, shortenedStateMasks, 0, stateMasksLength);
//		return shortenedStateMasks;
//	}

	/*
	 * @see SourceViewerConfiguration#getTextHover(ISourceViewer, String, int)
	 * @since 2.1
	 */
	public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType, int stateMask) {
//		JavaEditorTextHoverDescriptor[] hoverDescs= JavaPlugin.getDefault().getJavaEditorTextHoverDescriptors();
//		int i= 0;
//		while (i < hoverDescs.length) {
//			if (hoverDescs[i].isEnabled() &&  hoverDescs[i].getStateMask() == stateMask)
//				return new JavaEditorTextHoverProxy(hoverDescs[i], getEditor());
//			i++;
//		}

//		return null;
		return new ZTextHover(sourceViewer, contentType, getEditor());
	}

	/*
	 * @see SourceViewerConfiguration#getTextHover(ISourceViewer, String)
	 */
	public ITextHover getTextHover(ISourceViewer sourceViewer, String contentType) {
		return getTextHover(sourceViewer, contentType, ITextViewerExtension2.DEFAULT_HOVER_STATE_MASK);
	}
}
