/*
  Copyright (C) 2007 Petra Malik
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

import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.PrettyPrinter;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.session.AbstractCommand;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;

  public abstract class AbstractPrinterCommand extends AbstractCommand implements PrintPropertiesKeys
{

  protected Integer printTextWidth_ = null;
  protected Boolean printStructuredGoal_ = null;

  /**
   * When printing a pred/expr/para on the fly sectionName from doCompute is null,
   * yet we need to have a section name to print, usually something "on-the-fly".
   * This is to use the optable and latex markup function of this given section.
   */
  protected String onTheFlySectName_ = null;

  @Override
  protected void processProperties(SectionManager manager)
  {
    super.processProperties(manager);
    printStructuredGoal_ = manager.hasProperty(PROP_PRINTING_STRUCTURED_GOAL) ?
      manager.getBooleanProperty(PROP_PRINTING_STRUCTURED_GOAL) : null;
    onTheFlySectName_ = manager.hasProperty(PROP_PRINTING_ONTHEFLY_SECTION_NAME) ?
      manager.getProperty(PROP_PRINTING_ONTHEFLY_SECTION_NAME) : null;
    printTextWidth_ = manager.hasProperty(PROP_TXT_WIDTH) ?
      manager.getIntegerProperty(PROP_TXT_WIDTH) : null;
  }

  protected void processProperties(Properties props)
  {
    String prop = props.getProperty(PROP_PRINTING_STRUCTURED_GOAL);
    // properties might not come from the section manager (e.g., when called directly rather than through a command?)
    // give precedence to the properties set by the section manager properties, though
    if (prop != null && printStructuredGoal_ == null)
    {
      printStructuredGoal_ = "true".equals(prop);
    }
    prop = props.getProperty(PROP_PRINTING_ONTHEFLY_SECTION_NAME);
    if (prop != null && onTheFlySectName_ == null)
    {
      onTheFlySectName_ = prop;
    }
    prop = props.getProperty(PROP_TXT_WIDTH);
    if (prop != null && printTextWidth_ == null)
    {
      try {
        printTextWidth_ = Integer.valueOf(prop);
      }
      catch (NumberFormatException e) {
        printTextWidth_ = null;
      }
    }
  }

  /**
   * Creates a sequence of tokens for printing. It considers precedences by adding
   * parenthesis accordingly, as well as NLs depending on the underlying NL category
   * for each token involved in the token sequence.
   *
   * @param printer printer adaptor to be used by TokenSequence
   * @param term term to print
   * @param sectInfo section manager
   * @param sectionName section name
   * @param props properties
   * @return sequence of tokens to be print
   */
  public TokenSequence toUnicode(ZPrinter printer,
                                 Term term,
                                 SectionManager sectInfo,
                                 String sectionName,
                                 Properties props) throws PrintException
  {
    processProperties(props);
    Term tree = preprocess(term, sectInfo, sectionName);
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    tree.accept(precVisitor);
    TokenSequenceVisitor visitor = createTokenSequenceVisitor(sectInfo, printer, props);
    tree.accept(visitor);
    TokenSequence tseq = visitor.getResult();

    if (printTextWidth_ != null && printTextWidth_ > 0) {
      PrettyPrinter prettyPrinter = createPrettyPrinter(term, printTextWidth_);
      prettyPrinter.handleTokenSequence(tseq, 0);
    }
    visitor = null;
    tree = null;
    return tseq;
  }

  /**
   * Method to be called by the SectionManager Command: properties are the ones
   * processed via the SectionManager. toUnicode is the top-level method, which
   * might not be called as a SectionManager.Command. In this case, properties
   * are processed locally. 
   *
   * @param printer
   * @param term
   * @param sectInfo
   * @param sectionName
   * @param props
   * @return
   */
  protected TokenSequence doToUnicode(ZPrinter printer,
                                 Term term,
                                 SectionManager sectInfo,
                                 String sectionName,
                                 Properties props)
  {
    return null;
  }

  protected PrettyPrinter createPrettyPrinter(Term term, int textWidth)
  {
    return new PrettyPrinter(term, textWidth);
  }

  protected TokenSequenceVisitor createTokenSequenceVisitor(SectionInfo si, 
		  ZPrinter printer, Properties props)
  {
    return new TokenSequenceVisitor(si, printer, props);
  }

  protected Term preprocess(Term term,
                            SectionManager manager,
                            String section)
    throws PrintException
  {
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(manager);
    return toPrintTree(toPrintTree, term, section);
  }

  protected Term toPrintTree(AstToPrintTreeVisitor toPrintTree,
                             Term term,
                             String sectionName) throws PrintException
  {
    try {
      return toPrintTree.run(term, sectionName);
    }
    catch (CommandException exception) {
      String msg =
        "A command exception occurred while trying to print Unicode markup " +
        "for term within section " + sectionName;
      throw new PrintException(exception.getDialect(), msg, exception);
    }
  }
}
