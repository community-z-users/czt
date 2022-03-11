package net.sourceforge.czt.eclipse.ui.document;


/**
 * A document edit tracking service. The tracker install listeners on documents of all open editors
 * (text editors mostly). Then when the documents in these editors change (e.g. via user's
 * interaction), it fires the notifications about the change to interest listeners.
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
public interface IDocumentEditTracker
{
  
  /**
   * Adds a listener for document changes in editors. The listener will be asked whether it is
   * interested in changes from a specific editor/resource.
   * 
   * @param listener
   */
  public void addEditListener(IResourceDocumentListener listener);

  public void removeEditListener(IResourceDocumentListener listener);

}
