/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circustime;

import java.util.Properties;

import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.SectionInfo;

/**
 *
 * @author leo
 */
public class TokenSequenceVisitor 
  extends  net.sourceforge.czt.print.circus.TokenSequenceVisitor
{
  public TokenSequenceVisitor(SectionInfo si, ZPrinter printer, Properties props, 
		  net.sourceforge.czt.print.circus.WarningManager warningManager)
  {
    super(si, printer, props, warningManager);
    setZPrintVisitor(new CircusTimePrintVisitor(si, this, props, warningManager));
  }

}
