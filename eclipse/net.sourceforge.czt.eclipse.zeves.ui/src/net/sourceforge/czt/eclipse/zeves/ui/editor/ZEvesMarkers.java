package net.sourceforge.czt.eclipse.zeves.ui.editor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

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
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;

public class ZEvesMarkers {

	public static final String MARKER_ERROR = ZEvesUIPlugin.PLUGIN_ID + ".errorMarker";
	public static final String MARKER_RESULT = ZEvesUIPlugin.PLUGIN_ID + ".resultMarker";
	public static final String MARKER_RESULT_TRUE = ZEvesUIPlugin.PLUGIN_ID + ".resultTrueMarker";
	
	public static final String MARKER_COMMAND_STATUS = ZEvesUIPlugin.PLUGIN_ID + ".commandStatusMarker";
	public static final int STATUS_FINISHED = IMarker.SEVERITY_INFO;
	public static final int STATUS_UNFINISHED = IMarker.SEVERITY_WARNING;
	public static final int STATUS_FAILED = IMarker.SEVERITY_ERROR;
	
	public static final String MARKER_PROCESS = ZEvesUIPlugin.PLUGIN_ID + ".processMarker";
	public static final String MARKER_OUTPUT_SELECTION = ZEvesUIPlugin.PLUGIN_ID + ".outputSelectionMarker";
	
	private final IResource markerResource;
	private final IDocument document;
	
	private final List<MarkerInfo> pendingAddMarkers = new LinkedList<MarkerInfo>();
	private final List<MarkerInfo> pendingRemoveMarkers = new LinkedList<MarkerInfo>();
	private final Map<MarkerInfo, IMarker> addedMarkers = new HashMap<MarkerInfo, IMarker>();
	
	public ZEvesMarkers(IResource markerResource, IDocument document) {
		super();
		
		Assert.isNotNull(markerResource);
		
		this.markerResource = markerResource;
		this.document = document;
	}

	public MarkerInfo createErrorMarker(Position pos, String message) throws CoreException {
		return createErrorMarker(pos, message, IMarker.SEVERITY_ERROR);
	}
	
	public MarkerInfo createErrorMarker(Position pos, String message, int severity) throws CoreException {
		return createMarker(MARKER_ERROR, severity, pos, message);
	}
	
	public MarkerInfo createResultMarker(Position pos, String message) throws CoreException {
		return createMarker(MARKER_RESULT, IMarker.SEVERITY_INFO, pos, message);
	}
	
	public MarkerInfo createResultTrueMarker(Position pos, String message) throws CoreException {
		return createMarker(MARKER_RESULT_TRUE, IMarker.SEVERITY_INFO, pos, message);
	}
	
	public MarkerInfo createStatusMarker(Position pos, int type) throws CoreException {
		return createMarker(MARKER_COMMAND_STATUS, type, pos, null, false);
	}
	
	public MarkerInfo createProcessMarker(Position pos) throws CoreException {
		return createMarker(MARKER_PROCESS, 0, pos, null, false);
	}
	
	public MarkerInfo createMarker(String type, int severity, Position pos, String message)
			throws CoreException {
		return createMarker(type, severity, pos, message, true);
	}
	
	public MarkerInfo createMarker(String type, int severity, Position pos, String message,
			boolean lineMarker) throws CoreException {
		
		Map<String, Object> markerAttrs = new HashMap<String, Object>();
		
		markerAttrs.put(IMarker.SEVERITY, severity);
		markerAttrs.put(IMarker.PRIORITY, IMarker.PRIORITY_HIGH);
		
		if (pos != null) {
			int start = pos.getOffset();
			int end = pos.getOffset() + pos.getLength();
			
			if (lineMarker) {
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
			}
			
			markerAttrs.put(IMarker.CHAR_START, start);
			markerAttrs.put(IMarker.CHAR_END, end);
		}
		
		if (message != null) {
			markerAttrs.put(IMarker.MESSAGE, MarkerUtil.adaptMarkerValue(message));
		}
		
		MarkerInfo markerInfo = new MarkerInfo(type, markerAttrs);
		pendingAddMarkers.add(markerInfo);
		
		return markerInfo;
	}
	
	public void clearMarkers() throws CoreException {
		clearMarkers(markerResource);
	}
	
	public static void clearMarkers(final IResource markerResource) throws CoreException {
		IWorkspaceRunnable r = new IWorkspaceRunnable() {
			@Override
			public void run(IProgressMonitor monitor) throws CoreException {
				markerResource.deleteMarkers(MARKER_ERROR, true, 0);
				markerResource.deleteMarkers(MARKER_RESULT, true, 0);
				markerResource.deleteMarkers(MARKER_COMMAND_STATUS, true, 0);
				markerResource.deleteMarkers(MARKER_PROCESS, true, 0);
			}
		};

		try {
			markerResource.getWorkspace().run(r, null,IWorkspace.AVOID_UPDATE, null);
		} catch (CoreException ce) {
			ZEvesUIPlugin.getDefault().log(ce);
		}
	}
	
	public void deleteMarker(MarkerInfo markerInfo) {
		
		// remove from the pending list
		pendingAddMarkers.remove(markerInfo);
		
		// mark for removal
		pendingRemoveMarkers.add(markerInfo);
	}
	
	public void deleteMarkers(int offset) throws CoreException {
		deleteMarkers(markerResource, offset);
	}
	
	public static void deleteMarkers(IResource markerResource, int offset) throws CoreException {
		
		if (offset == 0) {
			// just clear everything
			clearMarkers(markerResource);
			return;
		}
		
		final List<IMarker> removeMarkers = new ArrayList<IMarker>();
		removeMarkers.addAll(findRemoveMarkers(markerResource, MARKER_ERROR, offset));
		removeMarkers.addAll(findRemoveMarkers(markerResource, MARKER_RESULT, offset));
		removeMarkers.addAll(findRemoveMarkers(markerResource, MARKER_COMMAND_STATUS, offset));
		removeMarkers.addAll(findRemoveMarkers(markerResource, MARKER_PROCESS, offset));
		
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
			ZEvesUIPlugin.getDefault().log(ce);
		}
	}
	
	private static List<IMarker> findRemoveMarkers(IResource markerResource, String type, int offset)
			throws CoreException {
		
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
		
		final List<MarkerInfo> addCopy = new ArrayList<MarkerInfo>(pendingAddMarkers);
		final List<MarkerInfo> removeCopy = new ArrayList<MarkerInfo>(pendingRemoveMarkers);
				
		pendingAddMarkers.clear();
		pendingRemoveMarkers.clear();
		
		final IResource resource = markerResource;
		
		IWorkspaceRunnable r = new IWorkspaceRunnable() {
			@Override
			public void run(IProgressMonitor monitor) throws CoreException {
				
				for (MarkerInfo markerInfo : removeCopy) {
					IMarker marker = addedMarkers.get(markerInfo);
					if (marker != null) {
						marker.delete();
						addedMarkers.remove(markerInfo);
					}
				}
				
				for (MarkerInfo markerInfo : addCopy) {
					IMarker marker = resource.createMarker(markerInfo.getType());
					marker.setAttributes(markerInfo.getAttributes());
					addedMarkers.put(markerInfo, marker);
				}
			}
		};

		try {
			resource.getWorkspace().run(r, null,IWorkspace.AVOID_UPDATE, null);
		} catch (CoreException ce) {
			ZEvesUIPlugin.getDefault().log(ce);
		}
	}
	
	public static class MarkerInfo {
		private final String type;
		private final Map<String, Object> attributes;
		
		public MarkerInfo(String type, Map<String, Object> attributes) {
			this.type = type;
			this.attributes = attributes;
		}

		public String getType() {
			return type;
		}

		public Map<String, Object> getAttributes() {
			return attributes;
		}
	}
	
}
