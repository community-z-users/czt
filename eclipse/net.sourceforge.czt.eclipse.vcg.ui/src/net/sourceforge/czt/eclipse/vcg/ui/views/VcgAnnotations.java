package net.sourceforge.czt.eclipse.vcg.ui.views;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.AbstractMap.SimpleEntry;
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
import org.eclipse.ui.texteditor.MarkerUtilities;

import net.sourceforge.czt.eclipse.ui.util.MarkerUtil;
import net.sourceforge.czt.eclipse.vcg.ui.VcgUIPlugin;


public class VcgAnnotations {

	public static final String MARKER_ERROR = VcgUIPlugin.PLUGIN_ID + ".errorMarker";
	
	private final IResource markerResource;
	private final IDocument document;
	
	private final List<Entry<String, Map<String, Object>>> pendingMarkers = 
			new ArrayList<Map.Entry<String, Map<String, Object>>>();
	
	public VcgAnnotations(IResource markerResource, IDocument document) {
		super();
		Assert.isNotNull(markerResource);
		
		this.markerResource = markerResource;
		this.document = document;
	}

	public void createErrorMarker(Position pos, String message) throws CoreException {

		createErrorMarker(pos, message, IMarker.SEVERITY_ERROR);
	}
	
	public void createErrorMarker(Position pos, String message, int severity) throws CoreException {

		createMarkupMessageMarker(MARKER_ERROR, severity, pos, message);
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
		
		markerAttrs.put(IMarker.MESSAGE, MarkerUtil.adaptMarkerValue(message));
		
		pendingMarkers.add(new SimpleEntry<String, Map<String, Object>>(type, markerAttrs));
		
//		MarkerUtilities.createMarker(markerResource, markerAttrs, type);
	}
	
	public void clearMarkers() throws CoreException {
		clearMarkers(markerResource);
	}
	
	public static void clearMarkers(IResource markerResource) throws CoreException {
		markerResource.deleteMarkers(MARKER_ERROR, false, 0);
	}
	
	public void deleteMarkers(int offset) throws CoreException {
		
		if (offset == 0) {
			// just clear everything
			clearMarkers();
			return;
		}
		
		final List<IMarker> removeMarkers = new ArrayList<IMarker>();
		removeMarkers.addAll(findRemoveMarkers(MARKER_ERROR, offset));
		
		IWorkspaceRunnable r = new IWorkspaceRunnable() {
			@Override
			public void run(IProgressMonitor monitor) throws CoreException {
				
				for (IMarker marker : removeMarkers) {
					marker.delete();
				}
			}
		};

		try {
			markerResource.getWorkspace().run(r, null,IWorkspace.AVOID_UPDATE, null);
		} catch (CoreException ce) {
			VcgUIPlugin.getDefault().log(ce);
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
			VcgUIPlugin.getDefault().log(ce);
		}
	}
	
}
