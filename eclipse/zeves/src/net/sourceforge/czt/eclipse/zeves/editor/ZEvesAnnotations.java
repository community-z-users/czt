package net.sourceforge.czt.eclipse.zeves.editor;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModelExtension;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.MarkerUtilities;


import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;

public class ZEvesAnnotations {

	public static final String MARKER_ERROR = ZEvesPlugin.PLUGIN_ID + ".errorMarker";
	public static final String MARKER_RESULT = ZEvesPlugin.PLUGIN_ID + ".resultMarker";
	public static final String MARKER_RESULT_TRUE = ZEvesPlugin.PLUGIN_ID + ".resultTrueMarker";
	
	private static final String COMMAND_ANN_PREFIX = ZEvesPlugin.PLUGIN_ID + ".annotation.command.";
	
	public static final String ANNOTATION_UNFINISHED = COMMAND_ANN_PREFIX + "unfinished";
	public static final String ANNOTATION_UNPROCESSED = COMMAND_ANN_PREFIX + "unprocessed";
	public static final String ANNOTATION_FAILED = COMMAND_ANN_PREFIX + "failed";
	public static final String ANNOTATION_FINISHED = COMMAND_ANN_PREFIX + "finished";
	
	private static final Object ZEVES_ANNOTATIONS = new Object();
	
	private final ITextEditor editor;
	private final IResource markerResource;
	private final IDocument document;
	
	private final List<Entry<String, Map<String, Object>>> pendingMarkers = 
			new ArrayList<Map.Entry<String, Map<String, Object>>>();
	
	private final Map<Annotation, Position> pendingAddAnnotations = new HashMap<Annotation, Position>();
	private final List<Annotation> pendingRemoveAnnotations = new ArrayList<Annotation>();
	
	public ZEvesAnnotations(ITextEditor editor, IResource markerResource, IDocument document) {
		super();
		
		Assert.isNotNull(editor);
		Assert.isNotNull(markerResource);
		
		this.editor = editor;
		this.markerResource = markerResource;
		this.document = document;
	}

	public void createErrorMarker(Position pos, String message) throws CoreException {

		createErrorMarker(pos, message, IMarker.SEVERITY_ERROR);
	}
	
	public void createErrorMarker(Position pos, String message, int severity) throws CoreException {

		createMarkupMessageMarker(MARKER_ERROR, severity, pos, message);
	}
	
	public void createResultMarker(Position pos, String message) throws CoreException {

		createMarkupMessageMarker(MARKER_RESULT, IMarker.SEVERITY_INFO, pos, message);
	}
	
	public void createResultTrueMarker(Position pos, String message) throws CoreException {

		createMarkupMessageMarker(MARKER_RESULT_TRUE, IMarker.SEVERITY_INFO, pos, message);
	}
	
	private void createMarkupMessageMarker(String type, int severity, Position pos, String message)
			throws CoreException {
		
		Map<String, Object> markerAttrs = new HashMap<String, Object>();
		
		markerAttrs.put(IMarker.SEVERITY, severity);
		markerAttrs.put(IMarker.PRIORITY, IMarker.PRIORITY_HIGH);
		
		if (pos != null) {
			int start = pos.getOffset();
			int end = pos.getOffset() + pos.getLength();
			
			try {
				if (document != null) {
					int line = document.getLineOfOffset(start);
					int line1 = line + 1; // for 1-relative
					markerAttrs.put(IMarker.LOCATION, "line " + line1);	
					markerAttrs.put(IMarker.LINE_NUMBER, line1);
					
					// trim the end of location to the end of line only
					int lineEnd = document.getLineOffset(line) + document.getLineLength(line);
					if (lineEnd < end) {
						end = lineEnd;
					}
					
				}
			} catch (BadLocationException ex) {
				// ignore
			}
			
			markerAttrs.put(IMarker.CHAR_START, start);
			markerAttrs.put(IMarker.CHAR_END, end);
		}
		
		markerAttrs.put(IMarker.MESSAGE, message);
		
		pendingMarkers.add(new SimpleEntry<String, Map<String, Object>>(type, markerAttrs));
		
//		MarkerUtilities.createMarker(markerResource, markerAttrs, type);
	}
	
	public void clearMarkers() throws CoreException {
		clearMarkers(markerResource);
		
		AnnotationModel annModel = getAnnotationModel();
		if (annModel != null) {
			annModel.removeAllAnnotations();
		}
	}
	
	public static void clearMarkers(IResource markerResource) throws CoreException {
		markerResource.deleteMarkers(MARKER_ERROR, true, 0);
		markerResource.deleteMarkers(MARKER_RESULT, true, 0);
	}
	
	public void deleteMarkers(int offset) throws CoreException {
		
		if (offset == 0) {
			// just clear everything
			clearMarkers();
			return;
		}
		
		final List<IMarker> removeMarkers = new ArrayList<IMarker>();
		removeMarkers.addAll(findRemoveMarkers(MARKER_ERROR, offset));
		removeMarkers.addAll(findRemoveMarkers(MARKER_RESULT, offset));
		
		final List<Annotation> removeAnns = new ArrayList<Annotation>();
		
		final AnnotationModel annModel = getAnnotationModel();
		if (annModel != null) {
			int docLength = document.getLength();
			
			@SuppressWarnings("unchecked")
			Iterator<Annotation> it = annModel.getAnnotationIterator(
					offset, (docLength - offset), true, true);
			while (it.hasNext()) {
				removeAnns.add(it.next());
			}
		}
		
		IWorkspaceRunnable r = new IWorkspaceRunnable() {
			@Override
			public void run(IProgressMonitor monitor) throws CoreException {
				
				for (IMarker marker : removeMarkers) {
					marker.delete();
				}
				
				if (annModel != null && !removeAnns.isEmpty()) {
					annModel.replaceAnnotations(
							removeAnns.toArray(new Annotation[removeAnns.size()]), 
							new HashMap<Object, Object>());
				}
			}
		};

		try {
			markerResource.getWorkspace().run(r, null,IWorkspace.AVOID_UPDATE, null);
		} catch (CoreException ce) {
			ZEvesPlugin.getDefault().log(ce);
		}
	}
	
	private List<IMarker> findRemoveMarkers(String type, int offset) throws CoreException {
		
		List<IMarker> remove = new ArrayList<IMarker>();
		
		IMarker[] markers = markerResource.findMarkers(type, true, 0);
		for (IMarker marker : markers) {
			int end = MarkerUtilities.getCharEnd(marker);
			if (end < 0) {
				continue;
			}
			
			if (end >= offset) {
				remove.add(marker);
			}
		}
		
		return remove;
	}
	
	public Annotation addAnnotation(Position pos, String annotationType) {
		if (pos == null) {
			return null;
		}
		
//		AnnotationModel annModel = getAnnotationModel();
//		if (annModel == null) {
//			return null;
//		}
		
		Annotation annotation = new Annotation(false);
		annotation.setType(annotationType);
		
//		annModel.addAnnotation(annotation, pos);
		
		pendingAddAnnotations.put(annotation, pos);
		
		return annotation;
	}
	
	public void removeAnnotation(Annotation annotation) {
		if (annotation == null) {
			return;
		}
		
//		AnnotationModel annModel = getAnnotationModel();
//		if (annModel == null) {
//			return;
//		}
//		
//		annModel.removeAnnotation(annotation);
		
		pendingAddAnnotations.remove(annotation);
		pendingRemoveAnnotations.add(annotation);
	}
	
	private AnnotationModel getAnnotationModel() {
		
		IAnnotationModel baseAnnotationModel = 
			editor.getDocumentProvider().getAnnotationModel(editor.getEditorInput());
		if (baseAnnotationModel == null) {
			return null;
		}
		
		// use modern models
		Assert.isTrue(baseAnnotationModel instanceof IAnnotationModelExtension);
		
		return getAnnotationModel((IAnnotationModelExtension) baseAnnotationModel, ZEVES_ANNOTATIONS); 
	}
	
	private AnnotationModel getAnnotationModel(IAnnotationModelExtension baseModel, Object key) {
		
		AnnotationModel model = (AnnotationModel) baseModel.getAnnotationModel(key);
		if (model == null) {
			model = new AnnotationModel();
			baseModel.addAnnotationModel(key, model);
		}
		
		return model;
	}
	
	public void flushPendingMarkers() {
		
		final List<Entry<String, Map<String, Object>>> markersCopy = 
				new ArrayList<Entry<String, Map<String,Object>>>(pendingMarkers);
		pendingMarkers.clear();
		
		final IResource resource = markerResource;
		
		IWorkspaceRunnable r = new IWorkspaceRunnable() {
			@Override
			public void run(IProgressMonitor monitor) throws CoreException {
				
				for (Entry<String, Map<String, Object>> markerEntry : markersCopy) {
					IMarker marker = resource.createMarker(markerEntry.getKey());
					marker.setAttributes(markerEntry.getValue());
				}
			}
		};

		try {
			resource.getWorkspace().run(r, null,IWorkspace.AVOID_UPDATE, null);
		} catch (CoreException ce) {
			ZEvesPlugin.getDefault().log(ce);
		}
	}
	
	public void flushPendingAnnotations() {
		
		Map<Annotation, Position> addCopy = new HashMap<Annotation, Position>(pendingAddAnnotations);
		Annotation[] removeCopy = pendingRemoveAnnotations.toArray(new Annotation[pendingRemoveAnnotations.size()]);

		pendingAddAnnotations.clear();
		pendingRemoveAnnotations.clear();
		
		AnnotationModel annModel = getAnnotationModel();
		if (annModel == null) {
			return;
		}

		annModel.replaceAnnotations(removeCopy, addCopy);
	}
	
}
