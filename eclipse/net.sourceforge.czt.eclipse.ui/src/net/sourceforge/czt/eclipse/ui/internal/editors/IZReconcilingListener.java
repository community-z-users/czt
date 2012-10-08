/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors;

import net.sourceforge.czt.eclipse.ui.internal.editors.parser.ParsedData;

import org.eclipse.core.runtime.IProgressMonitor;

/**
 * Interface of an object listening to Java reconciling.
 *
 * @author Chengdong Xu
 */
public interface IZReconcilingListener
{
  /**
   * Called before reconciling is started.
   */
  void aboutToBeReconciled();

  /**
   * Called after reconciling has been finished.
   * @param ast               the compilation unit AST or <code>null</code> if
   *                               the working copy was consistent or reconciliation has been cancelled
   * @param forced            <code>true</code> iff this reconciliation was forced
   * @param progressMonitor   the progress monitor
   */
  void reconciled(ParsedData parsedData, boolean forced,
      IProgressMonitor progressMonitor);
}
