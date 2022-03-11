package net.sourceforge.czt.eclipse.ui.document;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.ui.IEditorPart;

/**
 * A document listener designed to be used with changes originating from multiple editors/resources.
 * It allows to be queried whether the listener is interested in changes from a particular
 * editor/resource, and the event methods carry the source information as well.
 * 
 * @author Andrius Velykis
 */
public interface IResourceDocumentListener
{
  
  /**
   * Checks whether the events for the resource should be fired.
   * 
   * @param editor
   *          editor where the document events originated
   * @param resource
   *          resource being edited in the editor, or null if the resource is unavailable
   * @return true if the listener should be notified about the document events from the
   *         editor/resource, false otherwise
   */
  boolean isResourceInteresting(IEditorPart editor, IResource resource);
  
  /**
   * The manipulation described by the document event will be performed.
   * 
   * @param editor
   *          editor containing the document
   * @param resource
   *          the resource that the document represents
   * @param event
   *          the document event describing the document change
   */
  void documentAboutToBeChanged(IEditorPart editor, IResource resource, DocumentEvent event);

  /**
   * The manipulation described by the document event has been performed.
   * 
   * @param editor
   *          editor containing the document
   * @param resource
   *          the resource that the document represents
   * @param event
   *          the document event describing the document change
   */
  void documentChanged(IEditorPart editor, IResource resource, DocumentEvent event);
}
