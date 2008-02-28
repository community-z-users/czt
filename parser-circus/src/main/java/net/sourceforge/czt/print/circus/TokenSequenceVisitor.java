/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circus;

import java.util.Properties;

/**
 *
 * @author leo
 */
public class TokenSequenceVisitor 
  extends  net.sourceforge.czt.print.z.TokenSequenceVisitor
{
  public TokenSequenceVisitor(Properties props, WarningManager warningManager)
  {
    super();
    setZPrintVisitor(new CircusPrintVisitor(this, props, warningManager));
  }

}
