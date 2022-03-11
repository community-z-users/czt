package net.sourceforge.czt.zeves.response;

/**
 * An interface to provide printing facilities to Z/EVES Response XML elements. This
 * is used when the element to be printed (e.g. prover cmd) itself knows how to print
 * parts of its content, but for some of the content, e.g. command parameters, special
 * printing may be needed. This would allow using different printers to print the same
 * command, e.g. with unicode or LaTeX parameters.
 * 
 * @author Andrius Velykis
 */
public interface ZEvesResponsePrinter
{
  
  /**
   * Print the Z/EVES response XML element to a String
   * 
   * @param zEvesElem
   * @return
   */
  public String print(Object zEvesElem);
}
