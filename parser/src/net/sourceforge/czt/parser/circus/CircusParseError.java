/*
 * CircusParseResources.java
 *
 * Created on 22 March 2006, 14:11
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package net.sourceforge.czt.parser.circus;

import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.parser.util.ParseError;

/**
 * A parse error.
 */
public class CircusParseError extends ParseError
{
  private static String RESOURCE_NAME =
    "net.sourceforge.czt.parser.circus.CircusParseResources";

  public CircusParseError(CircusParseMessage msg,
                         Object[] params,
                         LocInfo locInfo)
  {
    super(msg.toString(), params, locInfo);
  }

  protected String getResourceName()
  {
    return RESOURCE_NAME;
  }
}
