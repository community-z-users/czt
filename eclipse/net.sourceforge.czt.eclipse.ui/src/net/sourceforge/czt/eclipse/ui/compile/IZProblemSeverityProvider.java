package net.sourceforge.czt.eclipse.ui.compile;

import net.sourceforge.czt.parser.util.CztError;

/**
 * An interface for classes that can provide severity for certain CZT errors. 
 * A user may have different preferences what to do with certain errors, 
 * e.g. ignore or raise them. The provider is used in compiler to check for 
 * certain problem severity.
 * 
 * @author Andrius Velykis
 */
public interface IZProblemSeverityProvider
{
  /**
   * Retrieves a specified severity (possibly different from error type) for 
   * the given error. The method should return null if it does not specify a 
   * special severity for the error.
   * 
   * @param dialect 
   *            Dialect that the problem was generated for
   * @param problem
   *            The given problem to find severity for
   * @return Severity of the problem, if available, null otherwise.
   */
  ZProblemSeverity getSeverity(String dialect, CztError problem);
}
