/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circus;

import java.util.Properties;
import net.sourceforge.czt.print.z.ZPrinter;

/**
 *
 * @author leo
 */
public class TokenSequenceVisitor 
  extends  net.sourceforge.czt.print.z.TokenSequenceVisitor
{
  public TokenSequenceVisitor(ZPrinter printer, Properties props, WarningManager warningManager)
  {
    super(printer);
    setZPrintVisitor(new CircusPrintVisitor(this, props, warningManager));
  }

}
