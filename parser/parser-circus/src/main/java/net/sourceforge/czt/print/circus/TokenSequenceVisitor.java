/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circus;

import java.util.Properties;

import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.SectionInfo;

/**
 *
 * @author leo
 */
public class TokenSequenceVisitor 
  extends  net.sourceforge.czt.print.z.TokenSequenceVisitor
{
  public TokenSequenceVisitor(SectionInfo si, ZPrinter printer, Properties props, WarningManager warningManager)
  {
    super(si, printer);
    setZPrintVisitor(new CircusPrintVisitor(si, this, props, warningManager));
  }

}
