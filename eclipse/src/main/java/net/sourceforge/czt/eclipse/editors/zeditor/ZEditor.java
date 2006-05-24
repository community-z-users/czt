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
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.OccurrencesFinderJob;
import net.sourceforge.czt.eclipse.editors.OccurrencesFinderJobCanceler;
import net.sourceforge.czt.eclipse.editors.ZCharacter;
import net.sourceforge.czt.eclipse.editors.ZLineBackgroundListener;
import net.sourceforge.czt.eclipse.editors.ZSourceViewerConfiguration;
import net.sourceforge.czt.eclipse.editors.actions.GoToDeclarationAction;
import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.outline.CztSegment;
import net.sourceforge.czt.eclipse.outline.ZContentOutlinePage;
import net.sourceforge.czt.eclipse.util.IZEncoding;
import net.sourceforge.czt.eclipse.util.IZFileType;
import net.sourceforge.czt.eclipse.util.PreferenceConstants;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.z.ast.ZDeclName;
import net.sourceforge.czt.z.ast.ZRefName;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.preference.IPreferenceStore;
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
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModelExtension;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.IVerticalRuler;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.jface.text.source.projection.ProjectionSupport;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.IPostSelectionProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IPartService;
import org.eclipse.ui.IWindowListener;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.texteditor.AbstractDecoratedTextEditorPreferenceConstants;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.IEditorStatusLine;
import org.eclipse.ui.views.contentoutline.ContentOutline;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

/**
 * @author Chengdong Xu
 */
public class ZEditor extends TextEditor {
	
	/**
	 * Internal implementation class for a change listener.
	 * @since 3.0
	 */
	protected abstract class AbstractSelectionChangedListener implements ISelectionChangedListener  {

		/**
		 * Installs this selection changed listener with the given selection provider. If
		 * the selection provider is a post selection provider, post selection changed
		 * events are the preferred choice, otherwise normal selection changed events
		 * are requested.
		 *
		 * @param selectionProvider
		 */
		public void install(ISelectionProvider selectionProvider) {
			if (selectionProvider == null)
				return;
			
			if (selectionProvider instanceof IPostSelectionProvider)  {
				IPostSelectionProvider provider= (IPostSelectionProvider) selectionProvider;
				provider.addPostSelectionChangedListener(this);
			} else  {
				selectionProvider.addSelectionChangedListener(this);
			}
		}

		/**
		 * Removes this selection changed listener from the given selection provider.
		 *
		 * @param selectionProvider the selection provider
		 */
		public void uninstall(ISelectionProvider selectionProvider) {
			if (selectionProvider == null)
				return;

			if (selectionProvider instanceof IPostSelectionProvider)  {
				IPostSelectionProvider provider= (IPostSelectionProvider) selectionProvider;
				provider.removePostSelectionChangedListener(this);
			} else  {
				selectionProvider.removeSelectionChangedListener(this);
			}
		}
	}

	/**
	 * Updates the Z outline page selection and this editor's range indicator.
	 *
	 * @since 3.0
	 */
	private class EditorSelectionChangedListener extends AbstractSelectionChangedListener {

		/*
		 * @see org.eclipse.jface.viewers.ISelectionChangedListener#selectionChanged(org.eclipse.jface.viewers.SelectionChangedEvent)
		 */
		public void selectionChanged(SelectionChangedEvent event) {
			ZEditor.this.selectionChanged();
		}
	}

	/**
	 * Updates the selection in the editor's widget with the selection of the outline page.
	 */
	private class OutlineSelectionChangedListener  extends AbstractSelectionChangedListener {
		public void selectionChanged(SelectionChangedEvent event) {
			doOutlineSelectionChanged(event);
		}
	}
	
	/**
	 * Internal activation listener.
	 * @since 3.0
	 */
	private class ActivationListener implements IWindowListener {

		/*
		 * @see org.eclipse.ui.IWindowListener#windowActivated(org.eclipse.ui.IWorkbenchWindow)
		 * @since 3.1
		 */
		public void windowActivated(IWorkbenchWindow window) {
			if (window == getEditorSite().getWorkbenchWindow() && fMarkOccurrenceAnnotations && isActivePart()) {
				fForcedMarkOccurrencesSelection= getSelectionProvider().getSelection();
//				SelectionListenerWithASTManager.getDefault().forceSelectionChange(ZEditor.this, (ITextSelection)fForcedMarkOccurrencesSelection);
			}
		}

		/*
		 * @see org.eclipse.ui.IWindowListener#windowDeactivated(org.eclipse.ui.IWorkbenchWindow)
		 * @since 3.1
		 */
		public void windowDeactivated(IWorkbenchWindow window) {
			if (window == getEditorSite().getWorkbenchWindow() && fMarkOccurrenceAnnotations && isActivePart())
				removeOccurrenceAnnotations();
		}

		/*
		 * @see org.eclipse.ui.IWindowListener#windowClosed(org.eclipse.ui.IWorkbenchWindow)
		 * @since 3.1
		 */
		public void windowClosed(IWorkbenchWindow window) {
		}

		/*
		 * @see org.eclipse.ui.IWindowListener#windowOpened(org.eclipse.ui.IWorkbenchWindow)
		 * @since 3.1
		 */
		public void windowOpened(IWorkbenchWindow window) {
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
	/**
	 * The outline page context menu id
	 */
	private String fOutlinerContextMenuId;
	/** The projection support */
	private ProjectionSupport fProjectionSupport;
	
	/**
	 * The editor selection changed listener.
	 *
	 * @since 3.0
	 */
	private EditorSelectionChangedListener fEditorSelectionChangedListener;
	/** The selection changed listener */
	protected AbstractSelectionChangedListener fOutlineSelectionChangedListener= new OutlineSelectionChangedListener();
	/**
	 * The internal shell activation listener for updating occurrences.
	 * @since 3.0
	 */
	private ActivationListener fActivationListener= new ActivationListener();
	
	/**
	 * Holds the current projection annotations.
	 */
	private Annotation[] fProjectionAnnotations;
	/**
	 * Holds the current occurrence annotations.
	 * @since 3.0
	 */
	private Annotation[] fOccurrenceAnnotations = null;
	/** The term highlight annotation */
	private Annotation fTermHighlightAnnotation = null;
	/**
	 * The document modification stamp at the time when the last
	 * occurrence marking took place.
	 * @since 3.1
	 */
	private long fMarkOccurrenceModificationStamp= IDocumentExtension4.UNKNOWN_MODIFICATION_STAMP;
	/**
	 * The document modification stamp at the time when the last
	 * term highlight marking took place.
	 * @since 3.1
	 */
	private long fMarkTermHighlightModificationStamp= IDocumentExtension4.UNKNOWN_MODIFICATION_STAMP;
	/**
	 * The selection used when forcing occurrence marking
	 * through code.
	 * @since 3.0
	 */
	private ISelection fForcedMarkOccurrencesSelection;
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
	/** The term currently highlighted */
	private Term fSelectedTerm = null; 
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
		System.out.println("ZEditor.createPartControl starts");
		ProjectionViewer viewer =(ProjectionViewer)getSourceViewer();
		fProjectionSupport = new ProjectionSupport(viewer,getAnnotationAccess(),getSharedColors());
		fProjectionSupport.install();
			
		//turn projection mode on
		viewer.doOperation(ProjectionViewer.TOGGLE);
			
		this.fAnnotationModel = viewer.getProjectionAnnotationModel();
		
		text = getSourceViewer().getTextWidget();
		
		fOccurrencesFinderJobCanceler = new OccurrencesFinderJobCanceler(this);
//		text.addLineBackgroundListener(this.fLineBackgroundListener);
		
		
		
//		IInformationControlCreator informationControlCreator= new IInformationControlCreator() {
//			public IInformationControl createInformationControl(Shell shell) {
//				boolean cutDown= false;
//				int style= cutDown ? SWT.NONE : (SWT.V_SCROLL | SWT.H_SCROLL);
//				return new DefaultInformationControl(shell, SWT.RESIZE | SWT.TOOL, style, new HTMLTextPresenter(cutDown));
//			}
//		};

//		fInformationPresenter= new InformationPresenter(informationControlCreator);
//		fInformationPresenter.setSizeConstraints(60, 10, true, true);
//		fInformationPresenter.install(getSourceViewer());

		fEditorSelectionChangedListener= new EditorSelectionChangedListener();
		fEditorSelectionChangedListener.install(getSelectionProvider());

//		if (fMarkOccurrenceAnnotations)
//			installOccurrencesFinder();

//		if (isSemanticHighlightingEnabled())
//			installSemanticHighlighting();

		PlatformUI.getWorkbench().addWindowListener(fActivationListener);
		System.out.println("ZEditor.createPartControl finishes");
	}
	
	/* (non-Javadoc)
	 * Method declared on AbstractTextEditor
	 */
	protected void initializeEditor() {
		super.initializeEditor();
		System.out.println("ZEditor.initializeEditor starts");
		goToDeclarationAction= new GoToDeclarationAction(CZTPlugin.getDefault().getResourceBundle(), "GoToDeclaration.", null); //$NON-NLS-1$
		goToDeclarationAction.setActionDefinitionId(this.GoToDeclarationAction_ID);
	}
	
    /* (non-Javadoc)
     * @see org.eclipse.ui.texteditor.AbstractTextEditor#createSourceViewer(org.eclipse.swt.widgets.Composite, org.eclipse.jface.text.source.IVerticalRuler, int)
     */
    protected ISourceViewer createSourceViewer(Composite parent,
            IVerticalRuler ruler, int styles)
    {
    	System.out.println("ZEditor.createSourceViewer starts");
        ISourceViewer viewer = new ProjectionViewer(parent, ruler, getOverviewRuler(), isOverviewRulerVisible(), styles);

    	// ensure decoration support has been created and configured.
    	getSourceViewerDecorationSupport(viewer);
    	System.out.println("ZEditor.createSourceViewer finishes");
    	return viewer;
    }
	
    public ISourceViewer getViewer() {
    	return getSourceViewer();
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
    
	/**
	 * Sets the outliner's context menu ID.
	 *
	 * @param menuId the menu ID
	 */
	protected void setOutlinerContextMenuId(String menuId) {
		fOutlinerContextMenuId= menuId;
	}
	
	/**
	 * Creates the outline page used with this editor.
	 *
	 * @return the created Java outline page
	 */
	protected ZContentOutlinePage createOutlinePage() {
		ZContentOutlinePage page= new ZContentOutlinePage(fOutlinerContextMenuId, this);
		fOutlineSelectionChangedListener.install(page);
		setOutlinePageInput(page, this.fParsedData);
		return page;
	}
	
	/**
	 * Informs the editor that its outliner has been closed.
	 */
	public void outlinePageClosed() {
		if (fOutlinePage != null) {
			fOutlineSelectionChangedListener.uninstall(fOutlinePage);
			fOutlinePage= null;
			resetHighlightRange();
		}
	}
	
	/**
	 * Synchronizes the outliner selection with the given element
	 * position in the editor.
	 *
	 * @param element the java element to select
	 */
	protected void synchronizeOutlinePage(int offset) {
		synchronizeOutlinePage(offset, true);
	}
	
	/**
	 * Synchronizes the outliner selection with the given element
	 * position in the editor.
	 *
	 * @param element the java element to select
	 * @param checkIfOutlinePageActive <code>true</code> if check for active outline page needs to be done
	 */
	protected void synchronizeOutlinePage(int offset, boolean checkIfOutlinePageActive) {
		if (fOutlinePage != null && offset > -1 && !(checkIfOutlinePageActive && isZOutlinePageActive())) {
			fOutlineSelectionChangedListener.uninstall(fOutlinePage);
			fOutlinePage.select(offset);
			fOutlineSelectionChangedListener.install(fOutlinePage);
		}
	}
	
	/**
	 * Synchronizes the outliner selection with the actual cursor
	 * position in the editor.
	 */
	public void synchronizeOutlinePageSelection() {
		synchronizeOutlinePage(getCursorOffset());
	}
	
	private void setOutlinePageInput(ZContentOutlinePage page, ParsedData data) {
		page.setInput(data);
	}
	
	protected boolean isActivePart() {
		IWorkbenchPart part= getActivePart();
		return part != null && part.equals(this);
	}

	private boolean isZOutlinePageActive() {
		IWorkbenchPart part= getActivePart();
		return part instanceof ContentOutline && ((ContentOutline)part).getCurrentPage() == fOutlinePage;
	}

	private IWorkbenchPart getActivePart() {
		IWorkbenchWindow window= getSite().getWorkbenchWindow();
		IPartService service= window.getPartService();
		IWorkbenchPart part= service.getActivePart();
		return part;
	}
	
	private int getCursorOffset() {
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
			offset = -1;
		}
		return offset;
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
		
		this.fAnnotationModel.modifyAnnotations(fProjectionAnnotations,newAnnotations,null);
		
		fProjectionAnnotations=annotations;
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
		if (term == null)
			return;
		else if (term instanceof ZDeclName)
			fOccurrencesFinderJob = new OccurrencesFinderJob(this, term);
		else if (term instanceof ZRefName) {
			ZDeclName declName = ((ZRefName)term).getDecl();
			if (declName == null)
				return;
			fOccurrencesFinderJob = new OccurrencesFinderJob(this, declName);
		}
		else
			return;
		
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
	
	public Annotation getTermHighlightAnnotation() {
		return this.fTermHighlightAnnotation;
	}
	
	public void setTermHighlightAnnotation(Annotation termHighlightAnnotation) {
		this.fTermHighlightAnnotation = termHighlightAnnotation;
	}
	
	public void removeTermHighlightAnnotation() {
		fMarkOccurrenceModificationStamp= IDocumentExtension4.UNKNOWN_MODIFICATION_STAMP;

		IDocumentProvider documentProvider= getDocumentProvider();
		if (documentProvider == null)
			return;

		IAnnotationModel annotationModel= documentProvider.getAnnotationModel(getEditorInput());
		if (annotationModel == null || fTermHighlightAnnotation == null)
			return;

		synchronized (getAnnotationLock(annotationModel)) {
			if (annotationModel instanceof IAnnotationModelExtension) {
				((IAnnotationModelExtension)annotationModel).replaceAnnotations(new Annotation[]{fTermHighlightAnnotation}, null);
			} else {
				annotationModel.removeAnnotation(fTermHighlightAnnotation);
			}
			fTermHighlightAnnotation = null;
		}
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
//		int offset = getCursorOffset();
//		setHighlightRange(offset);
		
//		if (this.fOutlinePage != null) {
//			this.fOutlinePage.select(offset);
//		}
		
//		markOccurrenceAnnotations(offset);
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
	
	/**
	 * React to changed selection.
	 *
	 * @since 3.0
	 */
	protected void selectionChanged() {
		if (getSelectionProvider() == null)
			return;
		if (getSelectionProvider().getSelection() instanceof TextSelection) {
			TextSelection textSelection = (TextSelection)getSelectionProvider().getSelection();
			removeTermHighlightAnnotation();
			removeOccurrenceAnnotations();
			// PR 39995: [navigation] Forward history cleared after going back in navigation history:
			// mark only in navigation history if the cursor is being moved (which it isn't if
			// this is called from a PostSelectionEvent that should only update the magnet)
			if (isActivePart() && (textSelection.getOffset() != 0 || textSelection.getLength() != 0))
				markInNavigationHistory();
			
			setSelection(textSelection, !isActivePart());
		}
//		updateStatusLine();
	}

	protected void setSelection(TextSelection selection, boolean moveCursor) {
		if (moveCursor) {
			this.selectAndReveal(selection.getOffset(),  selection.getLength(), selection.getOffset(), 0);
		}
		
		int cursorOffset = getCursorOffset();
		setHighlightRange(cursorOffset);
		markOccurrenceAnnotations(cursorOffset);
		
		if (!moveCursor) {
			boolean EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE = true;
//			EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE = getPreferenceStore().getBoolean(PreferenceConstants.EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE);
			if (EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE) {
				synchronizeOutlinePage(cursorOffset);
			}
		}
		
//		fSelectedTerm = null;
//		if (this.fParsedData != null) {
//			this.fTermSelector = new Selector(fParsedData.getSpec());
//			fSelectedTerm = fTermSelector.getTerm(position);
//		}
	}
	
	public void setOutlineSelection(int cursorOffset) {

		if (cursorOffset < 0)
			return;
		
		// set outliner selection
		if (fOutlinePage != null) {
			fOutlineSelectionChangedListener.uninstall(fOutlinePage);
			fOutlinePage.select(cursorOffset);
			fOutlineSelectionChangedListener.install(fOutlinePage);
		}
	}
	
	protected void doOutlineSelectionChanged(SelectionChangedEvent event) {

		CztSegment segment = null;

		ISelection selection= event.getSelection();
		Iterator iter= ((IStructuredSelection) selection).iterator();
		while (iter.hasNext()) {
			Object o= iter.next();
			if (o instanceof CztSegment) {
				segment = (CztSegment) o;
				break;
			}
		}
		
		if (!isActivePart() && CZTPlugin.getActivePage() != null)
			CZTPlugin.getActivePage().bringToTop(this);
		
		if (segment == null)
			return;
		Position position = segment.getNamePosition();
		TextSelection textSelection = new TextSelection(position.getOffset(), position.getLength());
		setSelection(textSelection, !isActivePart());
	}
	
	/** The <code>ZEditor</code> implementation of this 
	 * <code>AbstractTextEditor</code> method performs any extra 
	 * disposal actions required by the Z editor.
	 */
	public void dispose() {
		if (fOutlinePage != null)
			fOutlinePage.setInput(null);
		
//		if (fProjectionModelUpdater != null) {
//			fProjectionModelUpdater.uninstall();
//			fProjectionModelUpdater= null;
//		}
		
		if (fProjectionSupport != null) {
			fProjectionSupport.dispose();
			fProjectionSupport= null;
		}
		
		// cancel possible running computation
		fMarkOccurrenceAnnotations= false;
//		uninstallOccurrencesFinder();

//		uninstallOverrideIndicator();
		
//		uninstallSemanticHighlighting();

		if (fActivationListener != null) {
			PlatformUI.getWorkbench().removeWindowListener(fActivationListener);
			fActivationListener= null;
		}
		
		if (fEncodingSupport != null) {
			fEncodingSupport.dispose();
			fEncodingSupport= null;
		}

//		if (fBracketMatcher != null) {
//			fBracketMatcher.dispose();
//			fBracketMatcher= null;
//		}

//		if (fSelectionHistory != null) {
//			fSelectionHistory.dispose();
//			fSelectionHistory= null;
//		}
		
		if (fEditorSelectionChangedListener != null)  {
			fEditorSelectionChangedListener.uninstall(getSelectionProvider());
			fEditorSelectionChangedListener= null;
		}
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
				fOutlinePage= createOutlinePage();
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
		System.out.println("ZEditor.setFileType");
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
	
	public void setTermSelector(Selector selector) {
		this.fTermSelector = selector;
	}
	
	public Selector getTermSelector() {
		return this.fTermSelector;
	}
	
	/*
	 * @see AbstractTextEditor#handlePreferenceStoreChanged(PropertyChangeEvent)
	 */
	protected void handlePreferenceStoreChanged(PropertyChangeEvent event) {

		String property= event.getProperty();

		if (AbstractDecoratedTextEditorPreferenceConstants.EDITOR_TAB_WIDTH.equals(property)) {
			/*
			 * Ignore tab setting since we rely on the formatter preferences.
			 * We do this outside the try-finally block to avoid that EDITOR_TAB_WIDTH
			 * is handled by the sub-class (AbstractDecoratedTextEditor).
			 */
			return;
		}

		try {

			ISourceViewer sourceViewer= getSourceViewer();
			if (sourceViewer == null)
				return;
/*
			if (isJavaEditorHoverProperty(property))
				updateHoverBehavior();
*/
			boolean newBooleanValue= false;
			Object newValue= event.getNewValue();
			if (newValue != null)
				newBooleanValue= Boolean.valueOf(newValue.toString()).booleanValue();

			if (PreferenceConstants.EDITOR_SYNC_OUTLINE_ON_CURSOR_MOVE.equals(property)) {
				if (newBooleanValue)
					selectionChanged();
				return;
			}
/*
			if (PreferenceConstants.EDITOR_MARK_OCCURRENCES.equals(property)) {
				if (newBooleanValue != fMarkOccurrenceAnnotations) {
					fMarkOccurrenceAnnotations= newBooleanValue;
					if (!fMarkOccurrenceAnnotations)
						uninstallOccurrencesFinder();
					else
						installOccurrencesFinder();
				}
				return;
			}
			if (PreferenceConstants.EDITOR_MARK_TYPE_OCCURRENCES.equals(property)) {
				fMarkTypeOccurrences= newBooleanValue;
				return;
			}
			if (PreferenceConstants.EDITOR_MARK_METHOD_OCCURRENCES.equals(property)) {
				fMarkMethodOccurrences= newBooleanValue;
				return;
			}
			if (PreferenceConstants.EDITOR_MARK_CONSTANT_OCCURRENCES.equals(property)) {
				fMarkConstantOccurrences= newBooleanValue;
				return;
			}
			if (PreferenceConstants.EDITOR_MARK_FIELD_OCCURRENCES.equals(property)) {
				fMarkFieldOccurrences= newBooleanValue;
				return;
			}
			if (PreferenceConstants.EDITOR_MARK_LOCAL_VARIABLE_OCCURRENCES.equals(property)) {
				fMarkLocalVariableypeOccurrences= newBooleanValue;
				return;
			}
			if (PreferenceConstants.EDITOR_MARK_EXCEPTION_OCCURRENCES.equals(property)) {
				fMarkExceptions= newBooleanValue;
				return;
			}
			if (PreferenceConstants.EDITOR_MARK_METHOD_EXIT_POINTS.equals(property)) {
				fMarkMethodExitPoints= newBooleanValue;
				return;
			}
			if (PreferenceConstants.EDITOR_MARK_IMPLEMENTORS.equals(property)) {
				fMarkImplementors= newBooleanValue;
				return;
			}
			if (PreferenceConstants.EDITOR_STICKY_OCCURRENCES.equals(property)) {
				fStickyOccurrenceAnnotations= newBooleanValue;
				return;
			}
			if (SemanticHighlightings.affectsEnablement(getPreferenceStore(), event)) {
				if (isSemanticHighlightingEnabled())
					installSemanticHighlighting();
				else
					uninstallSemanticHighlighting();
				return;
			}

			if (JavaCore.COMPILER_SOURCE.equals(property)) {
				if (event.getNewValue() instanceof String)
					fBracketMatcher.setSourceVersion((String) event.getNewValue());
				// fall through as others are interested in source change as well.
			}
*/
//			((ZSourceViewerConfiguration)getSourceViewerConfiguration()).handlePropertyChangeEvent(event);
/*
			if (affectsOverrideIndicatorAnnotations(event)) {
				if (isShowingOverrideIndicators()) {
					if (fOverrideIndicatorManager == null)
						installOverrideIndicator(true);
				} else {
					if (fOverrideIndicatorManager != null)
						uninstallOverrideIndicator();
				}
				return;
			}

			if (PreferenceConstants.EDITOR_FOLDING_PROVIDER.equals(property)) {
				if (sourceViewer instanceof ProjectionViewer) {
					ProjectionViewer projectionViewer= (ProjectionViewer) sourceViewer;
					if (fProjectionModelUpdater != null)
						fProjectionModelUpdater.uninstall();
					// either freshly enabled or provider changed
					fProjectionModelUpdater= JavaPlugin.getDefault().getFoldingStructureProviderRegistry().getCurrentFoldingProvider();
					if (fProjectionModelUpdater != null) {
						fProjectionModelUpdater.install(this, projectionViewer);
					}
				}
				return;
			}

			if (DefaultCodeFormatterConstants.FORMATTER_TAB_SIZE.equals(property)
					|| DefaultCodeFormatterConstants.FORMATTER_INDENTATION_SIZE.equals(property)
					|| DefaultCodeFormatterConstants.FORMATTER_TAB_CHAR.equals(property)) {
				StyledText textWidget= sourceViewer.getTextWidget();
				int tabWidth= getSourceViewerConfiguration().getTabWidth(sourceViewer);
				if (textWidget.getTabs() != tabWidth)
					textWidget.setTabs(tabWidth);
				return;
			}

			if (PreferenceConstants.EDITOR_FOLDING_ENABLED.equals(property)) {
				if (sourceViewer instanceof ProjectionViewer) {
					new ToggleFoldingRunner().runWhenNextVisible();
				}
				return;
			}
*/
		} finally {
			super.handlePreferenceStoreChanged(event);
		}
		
		if (AbstractDecoratedTextEditorPreferenceConstants.SHOW_RANGE_INDICATOR.equals(property)) {
			// superclass already installed the range indicator
			Object newValue= event.getNewValue();
			ISourceViewer viewer= getSourceViewer();
			if (newValue != null && viewer != null) {
				if (Boolean.valueOf(newValue.toString()).booleanValue()) {
					// adjust the highlightrange in order to get the magnet right after changing the selection
					Point selection= viewer.getSelectedRange();
					adjustHighlightRange(selection.x, selection.y);
				}
			}

		}
	}
	
	/**
	 * Returns the boolean preference for the given key.
	 *
	 * @param store the preference store
	 * @param key the preference key
	 * @return <code>true</code> if the key exists in the store and its value is <code>true</code>
	 * @since 3.0
	 */
	private boolean getBoolean(IPreferenceStore store, String key) {
		return key != null && store.getBoolean(key);
	}
	
	/**
	 * Sets the given message as error message to this editor's status line.
	 *
	 * @param msg message to be set
	 */
	protected void setStatusLineErrorMessage(String msg) {
		IEditorStatusLine statusLine= (IEditorStatusLine) getAdapter(IEditorStatusLine.class);
		if (statusLine != null)
			statusLine.setMessage(true, msg, null);
	}

	/**
	 * Sets the given message as message to this editor's status line.
	 *
	 * @param msg message to be set
	 * @since 3.0
	 */
	protected void setStatusLineMessage(String msg) {
		IEditorStatusLine statusLine= (IEditorStatusLine) getAdapter(IEditorStatusLine.class);
		if (statusLine != null)
			statusLine.setMessage(false, msg, null);
	}
	
	/*
	 * @see StatusTextEditor#getStatusHeader(IStatus)
	 */
	protected String getStatusHeader(IStatus status) {
		if (fEncodingSupport != null) {
			String message= fEncodingSupport.getStatusHeader(status);
			if (message != null)
				return message;
		}
		return super.getStatusHeader(status);
	}

	/*
	 * @see StatusTextEditor#getStatusBanner(IStatus)
	 */
	protected String getStatusBanner(IStatus status) {
		if (fEncodingSupport != null) {
			String message= fEncodingSupport.getStatusBanner(status);
			if (message != null)
				return message;
		}
		return super.getStatusBanner(status);
	}

	/*
	 * @see StatusTextEditor#getStatusMessage(IStatus)
	 */
	protected String getStatusMessage(IStatus status) {
		if (fEncodingSupport != null) {
			String message= fEncodingSupport.getStatusMessage(status);
			if (message != null)
				return message;
		}
		return super.getStatusMessage(status);
	}

}
