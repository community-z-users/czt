package net.sourceforge.czt.eclipse.ui.internal.editors.zeditor;

import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.eclipse.ui.document.IDocumentEditTracker;
import net.sourceforge.czt.eclipse.ui.document.IResourceDocumentListener;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.internal.util.PartAdapter;
import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.ListenerList;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IWindowListener;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

/**
 * <p>
 * A document edit tracking service. The tracker install listeners on documents of all open editors
 * (text editors mostly). Then when the documents in these editors change (e.g. via user's
 * interaction), it fires the notifications about the change to interest listeners.
 * </p>
 * <p>
 * The interested parties may register listeners to be notified about the changes in documents
 * Listeners may indicate that they are interested in specific resources, see
 * {@link IResourceDocumentListener} for details.
 * </p>
 * <p>
 * The listeners should be light, otherwise they would slow down editing significantly. The tracking
 * is useful if files depend on the state of other files (e.g. parent sections in Z), and need to
 * notified when a dependency file changes.
 * </p>
 * @author Andrius Velykis
 * @see IResourceDocumentListener
 */
public class DocumentEditTracker implements IDocumentEditTracker
{

  private final Map<IEditorPart, DocumentChangeListenerSupport> editorListeners = 
      new HashMap<IEditorPart, DocumentChangeListenerSupport>();
  
  private final ListenerList interestedListeners = new ListenerList();
  
  /**
   * A listener to track when workbench windows are opened and closed. We need to attach
   * a part listener to all new windows, to listen to editors in these new windows.
   */
  private final IWindowListener windowListener;
  
  /**
   * A listener to track when editors are opened and closed, so to attach/detach document listeners
   */
  private final IPartListener2 partListener;
  
  public DocumentEditTracker()
  {
    
    this.windowListener = new IWindowListener()
    {
      
      @Override
      public void windowOpened(IWorkbenchWindow window) {}
      
      @Override
      public void windowDeactivated(IWorkbenchWindow window) {}
      
      @Override
      public void windowActivated(IWorkbenchWindow window)
      {
        window.getPartService().addPartListener(partListener);
      }
      
      @Override
      public void windowClosed(IWorkbenchWindow window)
      {
        window.getPartService().removePartListener(partListener);
      }
      
    };
    
    this.partListener = new PartAdapter()
    {
      @Override
      public void partActivated(IWorkbenchPartReference ref)
      {
        IEditorPart editor = getEditor(ref);
        if (editor != null) {
          getListener(editor, true);
        }
      }

      @Override
      public void partClosed(IWorkbenchPartReference ref)
      {
        IEditorPart editor = getEditor(ref);
        if (editor != null) {
          removeListener(editor);
        }
      }
    };
  }

  /**
   * Initializes the tracker - it starts listening for editor changes. Listeners are added to open
   * editors and any editors that are opened in the future.
   */
  public void init()
  {
    Display.getDefault().asyncExec(new Runnable()
    {

      @Override
      public void run()
      {
        // register part listener to be notified when editors are open/closed
        updatePartServiceListeners(true);
        
        // also register for all open editors
        for (IEditorPart editor : PlatformUtil.getOpenEditors()) {
          getListener(editor, true);
        }
      }
    });
  }
  
  /**
   * Updates (adds/removes) the part service listeners. The listeners are installed to listen when
   * editors are opened/closed. Multiple workbench windows are supported.
   * 
   * @param add
   *          if true, adds the listeners, otherwise removes.
   */
  private void updatePartServiceListeners(boolean add) {
    
    IWorkbench workbench = PlatformUI.getWorkbench();
    if (workbench == null) {
      return;
    }
    
    // add a window listener, which will attach part listeners to new windows
    if (add) {
      workbench.addWindowListener(windowListener);
    } else {
      workbench.removeWindowListener(windowListener);
    }

    // attach part listeners for opening/closing of windows
    for (IWorkbenchWindow window : workbench.getWorkbenchWindows()) {
      if (add) {
        window.getPartService().addPartListener(partListener);
      } else {
        window.getPartService().removePartListener(partListener);
      }
    }
  }
  
  public void dispose()
  {
    updatePartServiceListeners(false);

    for (IEditorPart editor : editorListeners.keySet()) {
      removeListener(editor);
    }
    editorListeners.clear();
    interestedListeners.clear();
  }

  /**
   * Retrieves an existing listener for the editor. If it does not exist, and <code>create</code>
   * flag is <code>true</code>, installs a new listener for the editor.
   * 
   * @param editor
   * @param create
   *          whether to install a new listener for the editor, if an old one is not found
   * @return
   */
  private DocumentChangeListenerSupport getListener(IEditorPart editor, boolean create)
  {

    DocumentChangeListenerSupport listener = editorListeners.get(editor);
    if (listener == null && create) {
      listener = installEditTracker(editor);
      if (listener != null) {
        editorListeners.put(editor, listener);
      }
    }

    return listener;
  }

  private IEditorPart getEditor(IWorkbenchPartReference ref)
  {
    IWorkbenchPart part = ref.getPart(false);
    if (part instanceof IEditorPart) {
      return (IEditorPart) part;
    }

    return null;
  }

  private void removeListener(IEditorPart editor)
  {
    DocumentChangeListenerSupport listener = getListener(editor, false);
    if (listener != null) {
      listener.dispose();
    }
  }

  /**
   * Installs an edit listener to the given editor. Upon document changes in the editor, if fires
   * notifications to all listeners registed with this {@link DocumentEditTracker}.
   * 
   * @param editor
   * @return
   */
  private DocumentChangeListenerSupport installEditTracker(final IEditorPart editor)
  {

    ITextViewer viewer = getTextViewer(editor);
    if (viewer == null) {
      // no text viewer - do not support at the moment
      return null;
    }

    DocumentChangeListenerSupport support = new DocumentChangeListenerSupport(viewer,
        new IDocumentListener()
        {

          @Override
          public void documentChanged(DocumentEvent event)
          {
            fireDocumentChangeEvent(editor, ZEditorUtil.getEditorResource(editor), event, false);
          }

          @Override
          public void documentAboutToBeChanged(DocumentEvent event)
          {
            fireDocumentChangeEvent(editor, ZEditorUtil.getEditorResource(editor), event, true);
          }
        });
    
    return support;
  }
  
  /**
   * From http://stackoverflow.com/questions/923342/get-itextviewer-from-ieditorpart-eclipse
   * 
   * @param editor
   * @return
   */
  private ITextViewer getTextViewer(IEditorPart editor)
  {
    ITextOperationTarget target = (ITextOperationTarget) editor.getAdapter(ITextOperationTarget.class);
    if (target instanceof ITextViewer) {
      return (ITextViewer) target;
    }
    
    return null;
  }
  
  private void fireDocumentChangeEvent(IEditorPart editor, IResource resource, DocumentEvent event,
      boolean aboutToBeChanged)
  {
    for (Object listenerObj : interestedListeners.getListeners()) {
      
      IResourceDocumentListener listener = (IResourceDocumentListener) listenerObj;
      
      if (listener.isResourceInteresting(editor, resource)) {
        
        if (aboutToBeChanged) {
          listener.documentAboutToBeChanged(editor, resource, event);
        } else {
          listener.documentChanged(editor, resource, event);
        }
      }
    }
  }
  
  /**
   * Adds a listener for document changes in editors. The listener will be asked whether it is
   * interested in changes from a specific editor/resource.
   * 
   * @param listener
   */
  @Override
  public void addEditListener(IResourceDocumentListener listener)
  {
    interestedListeners.add(listener);
  }

  @Override
  public void removeEditListener(IResourceDocumentListener listener)
  {
    interestedListeners.remove(listener);
  }
  
}
