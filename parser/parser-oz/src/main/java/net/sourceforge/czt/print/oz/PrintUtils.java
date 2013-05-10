/*
  Copyright (C) 2004, 2005, 2006, 2007 Petra Malik
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.print.oz;

import java.io.Writer;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Section;

/**
 * Utilities for printing Object-Z specifications given as an AST.
 *
 * @author Petra Malik
 */
public final class PrintUtils
{
  /**
   * Do not create instances of this class.
   */
  private PrintUtils()
  {
  }

  /**
   * Prints a given term (usually a Spec or Sect) in the specified
   * markup to the given writer.  The section information is used to
   * obtain the operator table and latex markup table needed for
   * printing, and should therefore be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>
   * and
   * <code>net.sourceforge.czt.parser.util.LatexMarkupTable.class</code>.
   *
   * This method may be used for terms like Spec and Sect that contain
   * a section header so that context information can be obtained from
   * the tree itself.  See {@link
   * #print(Term,Writer,SectionInfo,String,Markup)} for
   * writing trees that do not contain context information.
   */
  public static void print(Term term,
                           Writer out,
                           SectionManager sectInfo,
                           Markup markup) throws PrintException
  {
    final String sectionName = Section.STANDARD_TOOLKIT.getName();
    print(term, out, sectInfo, sectionName, markup);
  }

  public static void print(Term term,
                           Writer out,
                           SectionManager sectInfo,
                           String sectName,
                           Markup markup) throws PrintException
  {
    switch (markup) {
    case  LATEX:
      new LatexPrinterCommand().printLatex(term, out, sectInfo, sectName);
      break;
    case  UNICODE:
      new UnicodePrinterCommand().printUnicode(term, out, sectInfo, sectName);
      break;
    default:
      String message = "Attempt to print unsupported markup";
      throw new PrintException(sectInfo.getDialect(), message);
    }
  }
}
