package net.sourceforge.czt.eclipse.zeves.ui.commands;

import java.net.URI;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.eclipse.zeves.ui.editor.ZEvesMarkers;

import org.eclipse.core.filesystem.URIUtil;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;

public class ResourceUtil {

	public static String getPath(IResource resource) {
		return resource.getLocation().toOSString();
	}

	public static List<IFile> findFile(String filePath) {
		IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
		URI path = URIUtil.toURI(Path.fromOSString(filePath));
		IFile[] files = workspaceRoot.findFilesForLocationURI(path);
		return Arrays.asList(files);
	}
	
	public static void clearMarkers(Collection<String> filePaths) {
		
		// also remove all markers
		final List<IResource> clearResources = new ArrayList<IResource>();
		for (String filePath : filePaths) {
			clearResources.addAll(ResourceUtil.findFile(filePath));
		}
		
		if (clearResources.isEmpty()) {
			return;
		}
		
		IWorkspaceRunnable r = new IWorkspaceRunnable() {
			@Override
			public void run(IProgressMonitor monitor) throws CoreException {
				for (IResource resource : clearResources) {
					ZEvesMarkers.clearMarkers(resource);
				}
			}
		};

		try {
			clearResources.get(0).getWorkspace().run(r, null,IWorkspace.AVOID_UPDATE, null);
		} catch (CoreException ce) {
			ZEvesUIPlugin.getDefault().log(ce);
		}
	}
	
	public static void deleteMarkers(Map<String, Integer> pathUndoOffsets) {
		
		final Map<IFile, Integer> fileUndoOffsets = new LinkedHashMap<IFile, Integer>();
		for (Entry<String, Integer> pathOffset : pathUndoOffsets.entrySet()) {
			for (IFile file : ResourceUtil.findFile(pathOffset.getKey())) {
				fileUndoOffsets.put(file, pathOffset.getValue());
			}
		}
		
		if (fileUndoOffsets.isEmpty()) {
			return;
		}
		
		IWorkspaceRunnable r = new IWorkspaceRunnable() {
			@Override
			public void run(IProgressMonitor monitor) throws CoreException {
				for (Entry<IFile, Integer> fileOffset : fileUndoOffsets.entrySet()) {
					ZEvesMarkers.deleteMarkers(fileOffset.getKey(), fileOffset.getValue());
				}
			}
		};

		try {
			IFile file = fileUndoOffsets.keySet().iterator().next();
			file.getWorkspace().run(r, null,IWorkspace.AVOID_UPDATE, null);
		} catch (CoreException ce) {
			ZEvesUIPlugin.getDefault().log(ce);
		}
		
	}
	
}
