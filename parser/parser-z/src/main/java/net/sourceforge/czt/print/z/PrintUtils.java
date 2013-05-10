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

package net.sourceforge.czt.print.z;

import java.io.Writer;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.CztPrintString;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.util.Section;

/**
 * Utilities for printing Z specifications given as an AST.
 *
 * @author Petra Malik
 */
//TODO: why not have it as PrintUtils.xml in Parse Source for homogeneity, like ParseUtils?
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
   * @param term
   * @param out
   * @param sectInfo
   * @param markup
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
	assert sectInfo != null;
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

  /**
   * Prints the given name in the given markup using CztPrintString. It is interpreted
   * by the TermCommand protocol: tries it as ZSect first, then as Spec if fails.
   * Notice that the LaTeX printer might take LaTeX wrapping (e.g., preamble/postscript)
   * according to the section manager properties.
   * 
   * @param name resource name
   * @param sectInfo sect manager
   * @param markup which markup
   * @return the result as LaTeX, Unicode, or XML CztPrintString.
   * @throws CommandException if ZSect cannot be processed by the section manager, or if it cannot be printed.
   */
  public static CztPrintString printCztStringOf(String name, SectionManager sectInfo, Markup markup) throws CommandException
  {
    assert sectInfo != null && markup != null;

    // check the section manager knows about ZSect = throws CmdExp otherwise
    try
    {
      // get it as either ZSect or Spec (or Term)
      sectInfo.get(new Key<Term>(name, Term.class));
    }
    catch (CommandException e)
    {
      final String msg = "PRINT-UNKNOWN-SOURCE = " + name;
      sectInfo.getLogger().warning(msg);
      throw new CommandException(sectInfo.getDialect(), msg, e);
    }

    // prepare the printer's key depending on the markup 
    Key<? extends CztPrintString> key;
    switch (markup)
    {
      case LATEX:
        key = new Key<LatexString>(name, LatexString.class);
        break;
      case UNICODE:
        key = new Key<UnicodeString>(name, UnicodeString.class);
        break;
      case ZML:
        key = new Key<XmlString>(name, XmlString.class);
        break;
      default:
        final String msg = "PRINT-UNKNOWN-MARKUP = " + markup;
        sectInfo.getLogger().warning(msg);
        throw new CommandException(sectInfo.getDialect(), msg);
    }

    // compute the printed dcSpec
    CztPrintString output = null;
    try
    {
      // print it as either ZSpec or Spec (or Term) - either way surround it with LaTeX preamble if Markup.LATEX
      output = sectInfo.get(key);
    }
    catch (CommandException e)
    {
      final String msg = "PRINT-ERROR = " + markup + " for " + name;
      sectInfo.getLogger().warning(msg);
      throw new CommandException(sectInfo.getDialect(), msg, e);
    }
    assert output != null;

    // if not already there as a Source, add the string contents for name as a potential source
    Key<Source> source = new Key<Source>(name, Source.class);
    if (!sectInfo.isCached(source))
    {
      StringSource strSource = new StringSource(
              output.toString(), "CztPrintString["+key.getType().getSimpleName()+"]");
      sectInfo.put(source, strSource);
    }

    // return (non-null) result
    return output;
  }
}
