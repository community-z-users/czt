/*
 * ZEditor.java
 * Copyright (C) 2006 Chengdong Xu
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.eclipse.editors.zeditor;

import java.util.HashMap;
import java.util.List;
import java.util.ResourceBundle;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.OccurrencesFinderJob;
import net.sourceforge.czt.eclipse.editors.OccurrencesFinderJobCanceler;
import net.sourceforge.czt.eclipse.editors.ZCharacter;
import net.sourceforge.czt.eclipse.editors.ZLineBackgroundListener;
import net.sourceforge.czt.eclipse.editors.ZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.editors.actions.GoToDeclarationAction;
import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.outline.ZContentOutlinePage;
import net.sourceforge.czt.eclipse.util.IZEncoding;
import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.z.ast.ZRefName;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.BadPartitioningException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentExtension3;
import org.eclipse.jface.text.IDocumentExtension4;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ISynchronizable;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModelExtension;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.IVerticalRuler;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.jface.text.source.projection.ProjectionSupport;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.TextEditorAction;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

/**
 * @author Chengdong Xu
 */
public class ZEditor extends TextEditor {
	
	private class DefineFoldingRegionAction extends TextEditorAction {
		public DefineFoldingRegionAction(ResourceBundle bundle, String prefix, ITextEditor editor) {
			super(bundle, prefix, editor);
		}
		
		private IAnnotationModel getAnnotationModel(ITextEditor editor) {
			return (IAnnotationModel) editor.getAdapter(ProjectionAnnotationModel.class);
		}
		
		/*
		 * @see org.eclipse.jface.action.Action#run()
		 */
		public void run() {
			ITextEditor editor= getTextEditor();
			ISelection selection= editor.getSelectionProvider().getSelection();
			if (selection instanceof ITextSelection) {
				ITextSelection textSelection= (ITextSelection) selection;
				if (!textSelection.isEmpty()) {
					IAnnotationModel model= getAnnotationModel(editor);
					if (model != null) {
						
						int start= textSelection.getStartLine();
						int end= textSelection.getEndLine();
						
						try {
							IDocument document= editor.getDocumentProvider().getDocument(editor.getEditorInput());
							int offset= document.getLineOffset(start);
							int endOffset= document.getLineOffset(end + 1);
							Position position= new Position(offset, endOffset - offset);
							model.addAnnotation(new ProjectionAnnotation(), position);
						} catch (BadLocationException x) {
							// ignore
						}
					}
				}
			}
		}
	}

	/**
	 * Mutex for the reconciler. See https://bugs.eclipse.org/bugs/show_bug.cgi?id=63898
	 * for a description of the problem.
	 * <p>
	 * TODO remove once the underlying problem (https://bugs.eclipse.org/bugs/show_bug.cgi?id=66176) is solved.
	 * </p>
	 */
//	private final Object fReconcilerLock= new Object();
	
	private String fFileType = null;
	private Markup fMarkup = Markup.LATEX;
	private String fEncoding = null;
	/** The content outline page */
	private ZContentOutlinePage fOutlinePage;
	/** The projection support */
	private ProjectionSupport fProjectionSupport;
	/**
	 * Holds the current problem annotations.
	 */
	private Annotation[] oldAnnotations;
	/**
	 * Holds the current occurrence annotations.
	 * @since 3.0
	 */
	private Annotation[] fOccurrenceAnnotations = null;
	/**
	 * The document modification stamp at the time when the last
	 * occurrence marking took place.
	 * @since 3.1
	 */
	private long fMarkOccurrenceModificationStamp= IDocumentExtension4.UNKNOWN_MODIFICATION_STAMP;
	/**
	 * The region of the word under the caret used to when
	 * computing the current occurrence markings.
	 * @since 3.1
	 */
	private IRegion fMarkOccurrenceTargetRegion;
	/**
	 * Tells whether all occurrences of the element at the
	 * current caret location are automatically marked in
	 * this editor.
	 * @since 3.0
	 */
	private boolean fMarkOccurrenceAnnotations = true;
	private ProjectionAnnotationModel fAnnotationModel;
	/** The occurrences finder job */
	private OccurrencesFinderJob fOccurrencesFinderJob;
	/** The occurrences finder job canceler */
	private OccurrencesFinderJobCanceler fOccurrencesFinderJobCanceler;
	/** The parsed tree */
	private ParsedData fParsedData;
	/** The term selector */
	private Selector fTermSelector;
	/** The styled text */
	private StyledText text;
	private ZLineBackgroundListener fLineBackgroundListener = new ZLineBackgroundListener(this);
	
	protected GoToDeclarationAction goToDeclarationAction;
	protected String GoToDeclarationAction_ID = "net.sourceforge.czt.eclipse.editors.actions.GoToDeclaration";
	/**
	 * Mutex for the reconciler. See https://bugs.eclipse.org/bugs/show_bug.cgi?id=63898
	 * for a description of the problem.
	 * <p>
	 * TODO remove once the underlying problem (https://bugs.eclipse.org/bugs/show_bug.cgi?id=66176) is solved.
	 * </p>
	 */
	private final Object fReconcilerLock= new Object();
	
		
	public ZEditor() {
		super();
		setSourceViewerConfiguration(new ZSourceViewerConfiguration(this));
	}
	
	public void createPartControl(Composite parent) {
		super.createPartControl(parent);
		ProjectionViewer viewer =(ProjectionViewer)getSourceViewer();
		fProjectionSupport = new ProjectionSupport(viewer,getAnnotationAccess(),getSharedColors());
		fProjectionSupport.install();
			
		//turn projection mode on
		viewer.doOperation(ProjectionViewer.TOGGLE);
			
		this.fAnnotationModel = viewer.getProjectionAnnotationModel();
		
		text = getSourceViewer().getTextWidget();
		
		fOccurrencesFinderJobCanceler = new OccurrencesFinderJobCanceler(this);
//		text.addLineBackgroundListener(this.fLineBackgroundListener);
	}
	
	
    /* (non-Javadoc)
     * @see org.eclipse.ui.texteditor.AbstractTextEditor#createSourceViewer(org.eclipse.swt.widgets.Composite, org.eclipse.jface.text.source.IVerticalRuler, int)
     */
    protected ISourceViewer createSourceViewer(Composite parent,
            IVerticalRuler ruler, int styles)
    {
        ISourceViewer viewer = new ProjectionViewer(parent, ruler, getOverviewRuler(), isOverviewRulerVisible(), styles);

    	// ensure decoration support has been created and configured.
    	getSourceViewerDecorationSupport(viewer);
    	
    	return viewer;
    }
	
    public ISourceViewer getViewer() {
    	return getSourceViewer();
    }
    
	public void updateFoldingStructure(List<Position> positions)
	{
		Annotation[] annotations = new Annotation[positions.size()];
		
		//this will hold the new annotations along
		//with their corresponding positions
		HashMap<Annotation, Position> newAnnotations = new HashMap<Annotation, Position>();
		
		for(int i =0;i<positions.size();i++)
		{
			ProjectionAnnotation annotation = new ProjectionAnnotation();
			
			newAnnotations.put(annotation,positions.get(i));
			
			annotations[i]=annotation;
		}
		
		this.fAnnotationModel.modifyAnnotations(oldAnnotations,newAnnotations,null);
		
		oldAnnotations=annotations;
	}
	
	public Annotation[] getOccurrenceAnnotations() {
		return this.fOccurrenceAnnotations;
	}
	
	public void markOccurrenceAnnotations(int offset) {
		if (this.fParsedData == null)
			return;
		fTermSelector = this.fParsedData.getTermSelector();
		IDocument document = getDocumentProvider().getDocument(getEditorInput());
		Position word = findWordOfOffset(document, offset);
		Term term = fTermSelector.getTerm(word);
		if (term instanceof ZRefName) {
			fOccurrencesFinderJob = new OccurrencesFinderJob(this, ((ZRefName)term).getDecl());
		}
		else
			fOccurrencesFinderJob = new OccurrencesFinderJob(this, term);
		fOccurrencesFinderJob.run(new NullProgressMonitor());
	}
	
	public void setOccurrenceAnnotations(Annotation[] occurrenceAnnotations) {
		this.fOccurrenceAnnotations = occurrenceAnnotations;
	}
	
	public void removeOccurrenceAnnotations() {
		fMarkOccurrenceModificationStamp= IDocumentExtension4.UNKNOWN_MODIFICATION_STAMP;
		fMarkOccurrenceTargetRegion= null;

		IDocumentProvider documentProvider= getDocumentProvider();
		if (documentProvider == null)
			return;

		IAnnotationModel annotationModel= documentProvider.getAnnotationModel(getEditorInput());
		if (annotationModel == null || fOccurrenceAnnotations == null)
			return;

		synchronized (getAnnotationLock(annotationModel)) {
			if (annotationModel instanceof IAnnotationModelExtension) {
				((IAnnotationModelExtension)annotationModel).replaceAnnotations(fOccurrenceAnnotations, null);
			} else {
				for (int i= 0, length= fOccurrenceAnnotations.length; i < length; i++)
					annotationModel.removeAnnotation(fOccurrenceAnnotations[i]);
			}
			fOccurrenceAnnotations= null;
		}
	}
	
	/* (non-Javadoc)
	 * Method declared on AbstractTextEditor
	 */
	protected void initializeEditor() {
		super.initializeEditor();
		goToDeclarationAction= new GoToDeclarationAction(CZTPlugin.getDefault().getResourceBundle(), "GoToDeclaration.", null); //$NON-NLS-1$
		goToDeclarationAction.setActionDefinitionId(this.GoToDeclarationAction_ID);
	}
	
	/* (non-Javadoc)
	 * Method declared on AbstractTextEditor
	 */
	protected void editorContextMenuAboutToShow(IMenuManager menu) {
		super.editorContextMenuAboutToShow(menu);
		fillContextMenu(menu);
	}
	
	public void fillContextMenu(IMenuManager menuMgr) {		
		ITextSelection selection = (ITextSelection) getSelectionProvider().getSelection();
		goToDeclarationAction.setEnabled(selection.getLength() > 0);
	}
	
	public void installEncodingSupport() {
		super.installEncodingSupport();
		
		String encoding = null;
		
		/*
		 * Gets the encoding type based on the file type
		 */
		if ((fFileType == null) || fFileType.equals("")) {
		}
		else if (fFileType.equals(IZFileType.FILETYPE_LATEX)) {
		}
		else if (fFileType.equals(IZFileType.FILETYPE_UTF8)) {
			encoding = IZEncoding.ENCODING_UTF_8;
		}
		else if (fFileType.equals(IZFileType.FILETYPE_UTF16)) {
			encoding = IZEncoding.ENCODING_UTF_16;
		}
		else {
		}

		if (encoding != null) {
			this.fEncodingSupport.setEncoding(encoding);
			setEncoding(encoding);
		}
	}
	
	public void handleCursorPositionChanged() {
		super.handleCursorPositionChanged();
		
//		Annotation annotation = new Annotation("net.sourceforge.czt.eclipse.occurrence");
		
		String curPos = getCursorPosition();
		int colonPos = curPos.indexOf(":");
		// the line and column numbers are 1-based, so subtracted them by 1
		int line = Integer.parseInt(curPos.substring(0, colonPos - 1).trim()) - 1;
		int column = Integer.parseInt(curPos.substring(colonPos + 1).trim()) - 1;
		IDocument document = getDocumentProvider().getDocument(getEditorInput());
		int offset = -1;
		try {
			offset = document.getLineOffset(line) + column;
		} catch (BadLocationException ble) {
			return;
		}
		setHighlightRange(offset);
		
		if (this.fOutlinePage != null) {
			this.fOutlinePage.select(offset);
		}
		
		markOccurrenceAnnotations(offset);
	}
	
	public void setHighlightRange(int offset) {
		if (offset < 0) {
			this.resetHighlightRange();
			return;
		}
		
		try {
			ITypedRegion partition = null;
			IDocument document = getDocumentProvider().getDocument(getEditorInput());
			
			if (document instanceof IDocumentExtension3) {
				IDocumentExtension3 extension3= (IDocumentExtension3) document;
				
				try {
					partition = extension3.getPartition(CZTPlugin.Z_PARTITIONING, offset, false);
				}
				catch(BadPartitioningException be) {
					this.resetHighlightRange();
					return;
				}
			}
			else {
				partition = document.getPartition(offset);
			}

			setHighlightRange(partition.getOffset(), partition.getLength(), false);
		}
		catch (BadLocationException ble) {
			this.resetHighlightRange();
		}
	}

	/** The <code>ZEditor</code> implementation of this 
	 * <code>AbstractTextEditor</code> method performs any extra 
	 * disposal actions required by the Z editor.
	 */
	public void dispose() {
		if (fOutlinePage != null)
			fOutlinePage.setInput(null);
		
//		text.removeModifyListener(this.fModifyListener);
		
		super.dispose();
	}

	/** The <code>ZEditor</code> implementation of this 
	 * <code>AbstractTextEditor</code> method performs any extra 
	 * revert behavior required by the Z editor.
	 */
	public void doRevertToSaved() {
		super.doRevertToSaved();
	}
	
	/** The <code>ZEditor</code> implementation of this 
	 * <code>AbstractTextEditor</code> method performs any extra 
	 * save behavior required by the Z editor.
	 * 
	 * @param progressMonitor the progress monitor
	 */
	public void doSave(IProgressMonitor progressMonitor) {
		super.doSave(progressMonitor);
	}
	
	/** The <code>ZEditor</code> implementation of this 
	 * <code>AbstractTextEditor</code> method performs any extra 
	 * save as behavior required by the Z editor.
	 */
	public void doSaveAs() {
		super.doSaveAs();
	}
	
	/** The <code>JavaEditor</code> implementation of this 
	 * <code>AbstractTextEditor</code> method performs sets the 
	 * input of the outline page after AbstractTextEditor has set input.
	 * 
	 * @param input the editor input
	 * @throws CoreException in case the input can not be set
	 */ 
	public void doSetInput(IEditorInput input) throws CoreException {
		/**
		 * Set the file type first
		 */
		setFileType(input);
		super.doSetInput(input);
	}
	
	public void updateOutlinePage(ParsedData data) {
		if (fOutlinePage != null)
			fOutlinePage.setInput(getParsedData().getRoot());
	}
	
	/** The <code>ZEditor</code> implementation of this 
	 * <code>AbstractTextEditor</code> method performs gets
	 * the Z content outline page if request is for an 
	 * outline page.
	 * 
	 * @param required the required type
	 * @return an adapter for the required type or <code>null</code>
	 */ 
	public Object getAdapter(Class required) {
		if (IContentOutlinePage.class.equals(required)) {
			if (fOutlinePage == null) {
				fOutlinePage= new ZContentOutlinePage(getDocumentProvider(), this);
			}
			updateOutlinePage(getParsedData());
			return fOutlinePage;
		}
		
		if (fProjectionSupport != null) {
			Object adapter= fProjectionSupport.getAdapter(getSourceViewer(), required);
			if (adapter != null)
				return adapter;
		}
		
		return super.getAdapter(required);
	}
	
	public ZContentOutlinePage getContentOutlinePage() {
		return this.fOutlinePage;
	}
	
	/**
	 * Returns the mutex for the reconciler. See https://bugs.eclipse.org/bugs/show_bug.cgi?id=63898
	 * for a description of the problem.
	 * <p>
	 * TODO remove once the underlying problem (https://bugs.eclipse.org/bugs/show_bug.cgi?id=66176) is solved.
	 * </p>
	 * @return the lock reconcilers may use to synchronize on
	 */
	public Object getReconcilerLock() {
		return fReconcilerLock;
	}
	
	/**
	 * Returns the lock object for the given annotation model.
	 *
	 * @param annotationModel the annotation model
	 * @return the annotation model's lock object
	 * @since 3.0
	 */
	public Object getAnnotationLock(IAnnotationModel annotationModel) {
		if (annotationModel instanceof ISynchronizable)
			return ((ISynchronizable)annotationModel).getLockObject();
		else
			return annotationModel;
	}
	
	/**
	 * Returns the occurrences finder job
	 */
	public OccurrencesFinderJob getOccurrencesFinderJob() {
		return fOccurrencesFinderJob;
	}
	
	/**
	 * Returns the file type for the editor input
	 */
	public String getFileType() {
		return fFileType;
	}
	/**
	 * Sets the file type for the editor input
	 */
	private void setFileType(IEditorInput input) {
		if (input instanceof IFileEditorInput) {
			IFile file = ((IFileEditorInput) input).getFile();
			if (file != null)
				this.fFileType = file.getFileExtension().toLowerCase();
		}
		else {
			// if nothing was found, which should never happen
			this.fFileType = null;
		}
		
		if (IZFileType.FILETYPE_LATEX.equalsIgnoreCase(this.fFileType))
			setMarkup(Markup.LATEX);
		else if (IZFileType.FILETYPE_UTF8.equalsIgnoreCase(this.fFileType) ||
				IZFileType.FILETYPE_UTF16.equalsIgnoreCase(this.fFileType))
			setMarkup(Markup.UNICODE);
		else
			setMarkup(null);
	}
	
	/**
	 * Returns the markup of the editor input
	 */
	public Markup getMarkup() {
		return fMarkup;
	}
	
	/**
	 * Set the markup of the editor input
	 */
	private void setMarkup(Markup markup) {
		this.fMarkup = markup;
	}
	
	/**
	 * Returns the encoding of the editor input
	 */
	public String getEncoding() {
		return fEncoding;
	}
	
	/**
	 * Set the encoding of the editor input
	 */
	private void setEncoding(String encoding) {
		this.fEncoding = encoding;
	}	
	
	public ParsedData getParsedData() {
		if (this.fParsedData == null)
			this.fParsedData = new ParsedData(this.getEditorInput().getName());
		return this.fParsedData;
	}
	
	public void setParsedData(ParsedData data) {
		this.fParsedData = data;
	}
	
	public Position findWordOfOffset(IDocument document, int offset) {
		int regionStart = offset, regionEnd = offset;
		int line;
		int lineStart, lineEnd;
		try {
			if (!ZCharacter.isZWordPart(document.getChar(offset))) {
				return new Position(offset,1);
			}
			
			line = document.getLineOfOffset(offset);
			lineStart = document.getLineOffset(line);
			lineEnd = lineStart + document.getLineLength(line) - 1;
			for (; regionStart >= lineStart; regionStart--)
				if (!ZCharacter.isZWordPart(document.getChar(regionStart)))
					break;
			regionStart++;
			
			for (; regionEnd <= lineEnd; regionEnd++)
				if (!ZCharacter.isZWordPart(document.getChar(regionEnd))) {
					break;
				}
			regionEnd--;
					
			return new Position(regionStart, regionEnd - regionStart + 1);	
			
		} catch (BadLocationException ble) {
		}
		
		return null;
	}
}
