
package net.sourceforge.czt.eclipse.ui.internal.editors.zeditor;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.ui.IEditorPart;

import net.sourceforge.czt.eclipse.core.document.DocumentUtil;
import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.document.IDocumentEditTracker;
import net.sourceforge.czt.eclipse.ui.document.IResourceDocumentListener;
import net.sourceforge.czt.eclipse.ui.internal.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.ui.internal.util.VisiblePartRunner;
import net.sourceforge.czt.parser.util.SectParentResolver;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

/**
 * <p>
 * This class encapsulates functionality to notify Z editor about changes in its section parents.
 * </p>
 * <p>
 * When parsed, Z section can depend on a number of parents, which are located in different files.
 * During an editing session, these parent files could be updated, which would require the Z section
 * to be re-parsed (and re-typechecked) to account for the changes in parents.
 * </p>
 * <p>
 * The notifier installs listeners to a global {@link DocumentEditTracker}, which will notify about
 * live changes from the documents. Furthermore, it listens to workspace changes if files have been
 * modified.
 * </p>
 * <p>
 * When a notification about parent change is received, the editor is signaled to update the
 * document version, which means that there are incoming changes. Also, a reconcile is scheduled to
 * rebuild the Z section with new parent information.
 * </p>
 * 
 * @author Andrius Velykis
 */
public class ParentUpdateNotifier
{
  /**
   * Tracks the document version that the current list of parents represents. 
   */
  // Start with the parent version of -1, indicating that the current parents are these of an
  // unparsed document
  private BigInteger parentsVersion = BigInteger.valueOf(-1);
  
  /**
   * Contains document tracker listeners for each of parent paths.
   */
  private final Map<String, IResourceDocumentListener> editListeners = 
      new HashMap<String, IResourceDocumentListener>();
  
  private final ZEditor editor;
  private final VisiblePartRunner reconcileRunner;
  
  private final IResourceChangeListener resourceListener;

  public ParentUpdateNotifier(ZEditor zEditor)
  {
    super();
    this.editor = zEditor;
    
    this.reconcileRunner = new VisiblePartRunner(editor)
    {
      
      @Override
      protected void run(boolean immediate)
      {
        // if the editor is already visible, delay by 1 second, 
        // otherwise run immediately when visible.
        long delay = immediate ? 1000L : 0;
        editor.forceReconcile(delay);
      }
    };

    // add a listener to workspace as well
    // it will react to workspace changes, e.g. file operations
    this.resourceListener = new ResourceChangeListener();
    ResourcesPlugin.getWorkspace().addResourceChangeListener(resourceListener,
        IResourceChangeEvent.POST_CHANGE);
  }
  
  /**
   * Signals to update parent listeners with a fresh set of parsed information. The parents are
   * retrieved from the parsed sections and listeners are attached to receive notifications.
   * 
   * @param parsedData
   */
  public void updateParentListeners(ParsedData parsedData) {
    
    Set<String> parentPaths;
    try {
      parentPaths = getParentPaths(parsedData);
    } catch (CommandException ex) {
      // something's wrong, keep the old parents
      return;
    }
    
    updateParentListeners(parsedData.getDocumentVersion(), parentPaths);
  }
  
  /**
   * <p>
   * Updates the parent listeners with the given set of parent paths. Parent listeners for new paths
   * are added, and old path listeners are removed.
   * </p>
   * <p>
   * The method is synchronized to avoid updates to parent listeners from different parsed data at
   * the same time.
   * </p>
   * 
   * @param version
   * @param parentPaths
   */
  private synchronized void updateParentListeners(BigInteger version, Set<String> parentPaths) {
    
    if (parentsVersion.compareTo(version) > 0) {
      // already a bigger version used - ignore
      return;
    }
    
    Set<String> currentPaths = editListeners.keySet();
    
    // remove parents no longer available
    Set<String> removePaths = new HashSet<String>(currentPaths);
    removePaths.removeAll(parentPaths);
    
    // remove existing parents from the new set
    parentPaths.removeAll(currentPaths);
    
    IDocumentEditTracker editTracker = CztUIPlugin.getEditTracker();
    for (String remPath : removePaths) {
      editTracker.removeEditListener(editListeners.get(remPath));
      editListeners.remove(remPath);
    }
    
    for (String addPath : parentPaths) {
      IResourceDocumentListener listener = new VersionUpdateListener(addPath);
      editListeners.put(addPath, listener);
      editTracker.addEditListener(listener);
    }
    
    this.parentsVersion = version;
  }

  private static Set<String> getParentPaths(ParsedData parsedData) throws CommandException
  {
    
    Set<String> parents = getParents(parsedData);
    SectionInfo sectMan = parsedData.getSectionManager();
    
    Set<String> parentPaths = new HashSet<String>();
    
    // try to resolve parent paths from their sources
    for (String parent : parents) {
      Key<Source> key = new Key<Source>(parent, Source.class);
      if (sectMan.isCached(key)) {
        // check if it cached - it may be that the section was added as is to the section manager
        Source source = sectMan.get(key);
        String path = DocumentUtil.getPath(source);
        if (path != null) {
          parentPaths.add(path);
        }
      }
    }

    return parentPaths;
  }

  /*
   * Retrieves the parents from the parsed data. If the parsed data is invalid (e.g. not parsed, or
   * no sections), throws the CommandException.
   */
  private static Set<String> getParents(ParsedData parsedData) throws CommandException
  {
    Spec spec = parsedData.getSpec();
    if (spec == null) {
      throw new CommandException(parsedData.getSectionManager().getDialect(), "No specification available in the parsed data.");
    }

    Set<String> allParents = new HashSet<String>();

    boolean foundSect = false;
    for (Sect sect : spec.getSect()) {
      if (sect instanceof ZSect) {
        String sectName = ((ZSect) sect).getName();
        Set<String> parents = SectParentResolver.getParents(
            sectName, parsedData.getSectionManager());

        allParents.addAll(parents);

        foundSect = true;
      }
    }

    if (!foundSect) {
      throw new CommandException(parsedData.getSectionManager().getDialect(), "No sections available in the parsed specification.");
    }

    return allParents;
  }
  
  private void parentChanged() {
    // update the model with pending change
    editor.getModel().incrementDocumentVersion();
    
    // schedule a job to reconcile when the editor is next visible
    reconcileRunner.runWhenNextVisible();
  }
  
  public void dispose() {
    
    IDocumentEditTracker editTracker = CztUIPlugin.getEditTracker();
    for (IResourceDocumentListener listener : editListeners.values()) {
      editTracker.removeEditListener(listener);
    }
    
    editListeners.clear();
    
    reconcileRunner.cancel();
  }
  
  private class VersionUpdateListener extends PathDocumentListener {

    public VersionUpdateListener(String filePath)
    {
      super(Path.fromOSString(filePath));
    }

    @Override
    public void documentChanged(IEditorPart editor, IResource resource, DocumentEvent event)
    {
      parentChanged();
    }
  }
  
  
  /**
   * A workspace resource change listener that reacts to workspace file changes. If a changed file
   * is among the parents, the section is notified.
   * 
   * @author Andrius Velykis
   */
  private class ResourceChangeListener implements IResourceChangeListener {
    
    @Override
    public void resourceChanged(IResourceChangeEvent event)
    {
      try {
        event.getDelta().accept(new IResourceDeltaVisitor()
        {
          
          @Override
          public boolean visit(IResourceDelta delta) throws CoreException
          {
            IResource res = delta.getResource();
            if (delta.getFlags() == IResourceDelta.MARKERS) {
              // only markers changed - ignore
              return true;
            }
            
            IPath resPath = res.getLocation();
            if (resPath == null) {
              return true;
            }
            
            if (editListeners.containsKey(resPath.toOSString())) {
              // interested
              parentChanged();
              // one change is enough, since it will require full reparse
              // throw an exception to stop the visit
              throw new CoreException(Status.CANCEL_STATUS);
            }
            
            return true;
          }
        });
      }
      catch (CoreException e) {
        // ignore?
      }
    }
    
  }

}
