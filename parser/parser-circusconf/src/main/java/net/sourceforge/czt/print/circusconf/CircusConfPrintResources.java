/*
 * CircusPrintResources.java
 *
 * Created on 01 May 2007, 08:41
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circusconf;

import java.util.ListResourceBundle;

public class CircusConfPrintResources extends ListResourceBundle
{
  private static final Object[][] contents_ = computeContents();

  private static Object[][] computeContents()
  {
    Object[][] result = new Object[CircusConfPrintMessage.values().length][2];
    int i = 0;
    for (CircusConfPrintMessage msg : CircusConfPrintMessage.values()) {
      result[i][0] = msg.toString();
      result[i][1] = msg.getMessage();
      i++;
    }
    return result;
  }

  public Object[][] getContents()
  {
    return contents_;
  }
}
