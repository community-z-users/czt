/*
  Copyright (C) 2004, 2006, 2007 Petra Malik
  This file is part of the CZT project: http://czt.sourceforge.net

  The CZT project contains free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License as published
  by the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License along
  with CZT; if not, write to the Free Software Foundation, Inc.,
  59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.util.Factory;

public class LatexMarkupFunction
{
  /**
   * The name of the section to which this latex markup function belongs to.
   */
  private final String section_;

  /**
   * A mapping from String, a latex command, to MarkupDirective.
   * All pairs (string, directive) contained in this map should satisfy:
   * string.equals(directive.getCommand()).
   */
  private final Map<String,MarkupDirective> commandToDirective_ =
    new HashMap<String,MarkupDirective>();

  /**
   * A mapping from unicode String to MarkupDirective.
   * All pairs (string, directive) contained in this map should satisfy:
   * string.equals(directive.getUnicode()).
   */
  private final Map<String,MarkupDirective> unicodeToDirective_ =
    new HashMap<String,MarkupDirective>();

  /**
   * The directive defined in this section in the order they were
   * added.
   */
  private final List<MarkupDirective> directives_ =
    new ArrayList<MarkupDirective>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);

  /**
   * @throws NullPointerException if <code>section</code>
   *         is <code>null</code>.
   */
  public LatexMarkupFunction(String section)
  {
    if (section == null) {
      final String message
        = "A latex markup function must have a section name.";
      throw new NullPointerException(message);
    }
    section_ = section;
  }

  /**
   * Returns the name of the section of this markup function.
   */
  public String getSection()
  {
    return section_;
  }

  /**
   * Adds a new directive defined in the current section.
   * Note: This should not be used to add directives defined
   * in one of the ancestor sections.
   */
  public void add(Dialect d, Directive directive)
    throws MarkupException
  {
    final String command = directive.getCommand();
    final String unicode = directive.getUnicode();
    final MarkupDirective markupDirective =
      new MarkupDirective(d, directive, section_);
    if (getCommandDirective(command) != null) {
      reportError(getCommandDirective(command), markupDirective);
    }
    commandToDirective_.put(command, markupDirective);
    // uniqueness at Unicode won't work (e.g., 180 Unicode for 210 LaTex with Fuzz) --- we need to differentiate at printing
    //if (!unicodeToDirective_.containsKey(unicode))
    //{
      unicodeToDirective_.put(unicode, markupDirective);
    //}
    //else
    //{
    //  reportError(getUnicodeDirective(unicode), markupDirective);
    //}
    directives_.add(markupDirective);
  }

  public void add(LatexMarkupFunction markupFunction)
    throws MarkupException
  {
    for (MarkupDirective directive :
           markupFunction.commandToDirective_.values()) {
      final String command = directive.getCommand();
      if (getCommandDirective(command) != null) {
        checkDirectives(getCommandDirective(command), directive);
      }
      else {
        commandToDirective_.put(command, directive);
        final String unicode = directive.getUnicode();
        //if (!unicodeToDirective_.containsKey(unicode))
        //{
          unicodeToDirective_.put(unicode, directive);
        //}
        //else
        //{
        //  reportError(getUnicodeDirective(unicode), directive);
        //}
      }
      assert getCommandDirective(command) != null;
    }
  }

  public MarkupDirective getCommandDirective(String command)
  {
    return (MarkupDirective) commandToDirective_.get(command);
  }

  public MarkupDirective getUnicodeDirective(String unicode)
  {
    return (MarkupDirective) unicodeToDirective_.get(unicode);
  }

  /**
   * @throws MarkupException if both directives cannot live in the
   *         same namespace together.
   */
  private void checkDirectives(MarkupDirective directive1,
                               MarkupDirective directive2)
    throws MarkupException
  {
    assert directive1.getCommand().equals(directive2.getCommand());
    if (! directive1.equals(directive2)) {
      reportError(directive1, directive2);
    }
  }

  private void reportError(MarkupDirective directive1,
                           MarkupDirective directive2)
    throws MarkupException
  {
    throw new MarkupException(directive1, directive2);
  }

  public String toString()
  {
    return "LatexMarkupFunction for " + section_ + ": " +
      commandToDirective_.toString();
  }

  public LatexMarkupPara toAst(Factory factory)
  {
    LatexMarkupPara result = factory.createLatexMarkupPara();
    List<Directive> directiveList = result.getDirective();
    for (MarkupDirective directive : directives_) {
      assert directive.getSection().equals(section_);
      final Directive newDirective =
        factory.createDirective(directive.getCommand(),
                                directive.getUnicode(),
                                directive.getType());
      if (directive.getLine() != null) {
        LocAnn locAnn = factory.createLocAnn();
        locAnn.setLine(directive.getLine());
        newDirective.getAnns().add(locAnn);
      }
      directiveList.add(newDirective);
    }
    return result;
  }

  /**
   * Returns an iterator over the markup directives defined in this
   * markup function.
   */
  public Iterator<MarkupDirective> iterator()
  {
    return commandToDirective_.values().iterator();
  }
}
