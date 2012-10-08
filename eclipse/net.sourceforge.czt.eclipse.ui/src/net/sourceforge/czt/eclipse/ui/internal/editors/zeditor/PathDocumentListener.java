package net.sourceforge.czt.eclipse.ui.internal.editors.zeditor;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import net.sourceforge.czt.eclipse.ui.document.IResourceDocumentListener;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.ui.IEditorPart;

/**
 * <p>
 * An implementation of {@link IResourceDocumentListener} that checks if the resource path is among
 * the ones passed in the constructor.
 * </p>
 * <p>
 * The document event methods have default empty bodies. The extending classes should override where
 * necessary.
 * </p>
 * 
 * @author Andrius Velykis
 */
public class PathDocumentListener implements IResourceDocumentListener
{

  private final Set<IPath> interestingPaths;
  
  public PathDocumentListener(IPath interestingPath)
  {
    this(Collections.singleton(interestingPath));
  }
  
  public PathDocumentListener(Collection<? extends IPath> interestingPaths)
  {
    this.interestingPaths = new HashSet<IPath>(interestingPaths);
  }

  @Override
  public boolean isResourceInteresting(IEditorPart editor, IResource resource)
  {
    // ignore the editor - only check the resource
    
    if (resource == null) {
      return false;
    }
    
    return interestingPaths.contains(resource.getLocation());
  }

  @Override
  public void documentAboutToBeChanged(IEditorPart editor, IResource resource, DocumentEvent event)
  {
    // do nothing by default
  }

  @Override
  public void documentChanged(IEditorPart editor, IResource resource, DocumentEvent event)
  {
    // do nothing by default
  }

}
