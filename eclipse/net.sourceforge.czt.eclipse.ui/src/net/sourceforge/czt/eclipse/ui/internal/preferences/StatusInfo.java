/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.preferences;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IStatus;

/**
 * A settable IStatus. 
 * Can be an error, warning, info or ok. For error, info and warning states,
 * a message describes the problem.
 * 
 * @author Chengdong Xu
 */
public class StatusInfo implements IStatus
{

  public static final IStatus OK_STATUS = new StatusInfo();

  private String fStatusMessage;

  private int fSeverity;

  /**
   * Creates a status set to OK (no message)
   */
  public StatusInfo()
  {
    this(OK, null);
  }

  /**
   * Creates a status .
   * @param severity The status severity: ERROR, WARNING, INFO and OK.
   * @param message The message of the status. Applies only for ERROR,
   * WARNING and INFO.
   */
  public StatusInfo(int severity, String message)
  {
    fStatusMessage = message;
    fSeverity = severity;
  }

  /**
   *  Returns if the status' severity is OK.
   *  @see org.eclipse.core.runtime.IStatus#isOK()
   */
  public boolean isOK()
  {
    return fSeverity == IStatus.OK;
  }

  /**
   *  Returns if the status' severity is INFO.
   */
  public boolean isInfo()
  {
    return fSeverity == IStatus.INFO;
  }

  /**
   *  Returns if the status' severity is WARNING.
   */
  public boolean isWarning()
  {
    return fSeverity == IStatus.WARNING;
  }

  /**
   *  Returns if the status' severity is ERROR.
   */
  public boolean isError()
  {
    return fSeverity == IStatus.ERROR;
  }

  /**
   * @see org.eclipse.core.runtime.IStatus#getMessage()
   */
  public String getMessage()
  {
    return fStatusMessage;
  }

  /**
   * Sets the status to OK.
   */
  public void setOK()
  {
    fStatusMessage = null;
    fSeverity = IStatus.OK;
  }

  /**
   * Sets the status to INFO.
   * @param infoMessage The info message (can be empty, but not null)
   */
  public void setInfo(String infoMessage)
  {
    Assert.isNotNull(infoMessage);
    fStatusMessage = infoMessage;
    fSeverity = IStatus.INFO;
  }

  /**
   * Sets the status to WARNING.
   * @param warningMessage The warning message (can be empty, but not null)
   */
  public void setWarning(String warningMessage)
  {
    Assert.isNotNull(warningMessage);
    fStatusMessage = warningMessage;
    fSeverity = IStatus.WARNING;
  }

  /**
   * Sets the status to ERROR.
   * @param errorMessage The error message (can be empty, but not null)
   */
  public void setError(String errorMessage)
  {
    Assert.isNotNull(errorMessage);
    fStatusMessage = errorMessage;
    fSeverity = IStatus.ERROR;
  }

  /*
   * @see org.eclipse.core.runtime.IStatus#matches(int)
   */
  public boolean matches(int severityMask)
  {
    return (fSeverity & severityMask) != 0;
  }

  /**
   * Returns always <code>false</code>
   * @see org.eclipse.core.runtime.IStatus#isMultiStatus()
   */
  public boolean isMultiStatus()
  {
    return false;
  }

  /**
   * @see org.eclipse.core.runtime.IStatus#getSeverity()
   */
  public int getSeverity()
  {
    return fSeverity;
  }

  /**
   * Returns always <code>null</code>
   * @see org.eclipse.core.runtime.IStatus#getException()
   */
  public Throwable getException()
  {
    return null;
  }

  /**
   * Returns always the error severity
   * @see org.eclipse.core.runtime.IStatus#getCode()
   */
  public int getCode()
  {
    return fSeverity;
  }

  /**
   * Returns always <code>null</code>
   * @see org.eclipse.core.runtime.IStatus#getChildren()
   */
  public IStatus[] getChildren()
  {
    return new IStatus[0];
  }

  /**
   * @see org.eclipse.core.runtime.IStatus#getPlugin()
   */
  public String getPlugin()
  {
    return CztUIPlugin.PLUGIN_ID;
  }
}
