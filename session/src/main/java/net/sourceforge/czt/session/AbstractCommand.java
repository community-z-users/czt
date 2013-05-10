/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.session;

import java.util.logging.Logger;

/**
 * Command superclass that respects the section manager's tracing protocols.
 * @author Leo Freitas
 */
public abstract class AbstractCommand implements Command {

  private final static Logger logger_ = Logger.getLogger(SectionManager.class.getName());

  /**
   * Logs tracing information for this command to the underlying section
   * manager. It respects the tracing protocol that commands should always
   * log "finest" messages to avoid too verbose traces.
   * @param msg the message to log
   */
  protected static void traceLog(String msg)
  {
    logger_.finest(msg);
  }

  /**
   * Some complicated commands might require top-level trace information.
   * @param msg the log message (as INFO)
   */
  protected static void traceInfo(String msg)
  {
    logger_.info(msg);
  }

  /**
   * Performs the commands computation of the required resource within
   * the section manager known to this command. For tracing, one should
   * call the debug method appropriately.
   * @param name the resource name
   * @param manager
   * @return if command is successful or not. Deprecated?
   * @throws CommandException if any problem occurs.
   */
  @Override
  public final boolean compute(String name, SectionManager manager)
    throws CommandException
  {
	if (manager == null) throw new NullPointerException();
    processProperties(manager);
    return doCompute(name, manager);
  }

  protected abstract boolean doCompute(String name, SectionManager manager) throws CommandException;

  /**
   * Pass section manager to enable derived classes to preprocess any property of interest
   * @param manager
   */
  protected void processProperties(SectionManager manager)
  {
    // do nothing
  }
}
