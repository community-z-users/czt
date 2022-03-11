/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.reconciler.DirtyRegion;
import org.eclipse.jface.text.reconciler.IReconcilingStrategy;
import org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension;

/**
 * A reconciling strategy consisting of a sequence of internal reconciling strategies.
 * By default, all requests are passed on to the contained strategies.
 *
 * @author Chengdong Xu
 */
public class CompositeReconcilingStrategy
    implements
      IReconcilingStrategy,
      IReconcilingStrategyExtension
{
  /** The list of internal reconciling strategies. */
  private List<IReconcilingStrategy> fStrategies = new ArrayList<IReconcilingStrategy>();

  /**
   * Creates a new, empty composite reconciling strategy.
   */
  public CompositeReconcilingStrategy()
  {
  }

  /**
   * Sets the reconciling strategies for this composite strategy.
   *
   * @param strategies the strategies to be set or <code>null</code>
   */
  public void setReconcilingStrategies(List<IReconcilingStrategy> strategies)
  {
    fStrategies = strategies;
  }

  /**
   * Returns the previously set stratgies or <code>null</code>.
   *
   * @return the contained strategies or <code>null</code>
   */
  public List<IReconcilingStrategy> getReconcilingStrategies()
  {
    return fStrategies;
  }
  
  /**
   * Adds a reconciling strategy to the list of strategies.
   *
   * @param strategy the strategy to be added to the list of strategies
   */
  public void addReconcilingStrategy(IReconcilingStrategy strategy)
  {
    if (fStrategies == null)
      fStrategies = new ArrayList<IReconcilingStrategy>();
    if (fStrategies.contains(strategy))
      return;
    fStrategies.add(strategy);
  }

  /**
   * Removes a reconciling strategy from the list of strategies.
   *
   * @param strategy the strategy to be removed from the list of strategies
   */
  public void removeReconcilingStrategy(IReconcilingStrategy strategy)
  {
    if (fStrategies == null)
      fStrategies = new ArrayList<IReconcilingStrategy>();
    fStrategies.remove(strategy);
  }

  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.IRegion)
   */
  public void reconcile(IRegion partition)
  {
    if (fStrategies == null)
      return;

    for (IReconcilingStrategy strategy : fStrategies)
      strategy.reconcile(partition);
  }

  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#reconcile(org.eclipse.jface.text.reconciler.DirtyRegion, org.eclipse.jface.text.IRegion)
   */
  public void reconcile(DirtyRegion dirtyRegion, IRegion subRegion)
  {
    if (fStrategies == null)
      return;

    for (IReconcilingStrategy strategy : fStrategies)
      strategy.reconcile(dirtyRegion, subRegion);
  }

  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategy#setDocument(org.eclipse.jface.text.IDocument)
   */
  public void setDocument(IDocument document)
  {
    if (fStrategies == null)
      return;

    for (IReconcilingStrategy strategy : fStrategies)
      strategy.setDocument(document);
  }

  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#initialReconcile()
   */
  public void initialReconcile()
  {
    if (fStrategies == null)
      return;

    for (IReconcilingStrategy strategy : fStrategies) {
      if (strategy instanceof IReconcilingStrategyExtension) {
        IReconcilingStrategyExtension extension = (IReconcilingStrategyExtension) strategy;
        extension.initialReconcile();
      }
    }
  }

  /*
   * @see org.eclipse.jface.text.reconciler.IReconcilingStrategyExtension#setProgressMonitor(org.eclipse.core.runtime.IProgressMonitor)
   */
  public void setProgressMonitor(IProgressMonitor monitor)
  {
    if (fStrategies == null)
      return;

    for (IReconcilingStrategy strategy : fStrategies) {
      if (strategy instanceof IReconcilingStrategyExtension) {
        IReconcilingStrategyExtension extension = (IReconcilingStrategyExtension) strategy;
        extension.setProgressMonitor(monitor);
      }
    }
  }

}
