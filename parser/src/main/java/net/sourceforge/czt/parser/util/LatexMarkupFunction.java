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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.DirectiveType;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.util.Factory;

public class LatexMarkupFunction
{
  /**
   * The name of the section to which this latex markup function belongs to.
   */
  private String section_;

  /**
   * A mapping from String, a latex command, to MarkupDirective.
   * All pairs (string, directive) contained in this map should satisfy:
   * string.equals(directive.getCommand()).
   */
  private Map<String,MarkupDirective> commandToDirective_ =
    new HashMap<String,MarkupDirective>();

  /**
   * A mapping from unicode String to MarkupDirective.
   * All pairs (string, directive) contained in this map should satisfy:
   * string.equals(directive.getUnicode()).
   */
  private Map<String,MarkupDirective> unicodeToDirective_ =
    new HashMap<String,MarkupDirective>();

  /**
   * The directive defined in this section in the order they were
   * added.
   */
  private List<MarkupDirective> directives_ =
    new ArrayList<MarkupDirective>();

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
  public void add(Directive directive)
    throws MarkupException
  {
    final String command = directive.getCommand();
    final String unicode = directive.getUnicode();
    final MarkupDirective markupDirective =
      new MarkupDirective(directive, section_);
    if (commandToDirective_.get(command) != null) {
      String message = "Command " + command +
        " defined twice in section " + section_;
      message += "\n" + commandToDirective_.get(command) +
        "\n" + markupDirective;
      throw new MarkupException(message);
    }
    commandToDirective_.put(command, markupDirective);
    unicodeToDirective_.put(unicode, markupDirective);
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
        unicodeToDirective_.put(directive.getUnicode(), directive);
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
      String message = "Command " + directive1.getCommand() +
        " defined twice in section " + section_;
      message += "\n" + directive1 + "\n" + directive2;
      throw new MarkupException(message);
    }
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

  /**
   * A markup directive.
   */
  public static class MarkupDirective
  {
    private String command_;
    private String unicode_;
    private DirectiveType type_;
    private String section_;
    private BigInteger lineNr_ = null;

    /**
     * @throws NullPointerException if one of the arguments
     *         is <code>null</code>.
     */
    public MarkupDirective(String command,
                           String unicode,
                           DirectiveType type,
                           String section,
                           BigInteger lineNr)
    {
      command_ = command;
      unicode_ = unicode;
      type_ = type;
      section_ = section;
      lineNr_ = lineNr;
      checkMembersNonNull();
    }

    /**
     * @throws NullPointerException if <code>directive</code> or
     *         <code>section</code> is <code>null</code>; or if
     *         the command, unicode, or type of the given directive
     *         is <code>null</code>.
     */
    public MarkupDirective(Directive directive, String section)
    {
      command_ = directive.getCommand();
      unicode_ = directive.getUnicode();
      type_ = directive.getType();
      section_ = section;
      LocAnn locAnn = directive.getAnn(LocAnn.class);
      if (locAnn != null) {
        lineNr_ = locAnn.getLine();
      }
      checkMembersNonNull();
    }

    /**
     * Throws a <code>NullPointerException</code> if one of the member
     * variables is <code>null</code>.
     */
    private void checkMembersNonNull()
    {
      if (command_ == null || unicode_ == null ||
          type_ == null || section_ == null) {
        throw new NullPointerException();
      }
    }

    public BigInteger getLine()
    {
      return lineNr_;
    }

    public String getSection()
    {
      return section_;
    }

    public String getCommand()
    {
      return command_;
    }

    public String getUnicode()
    {
      return unicode_;
    }

    public DirectiveType getType()
    {
      return type_;
    }

    /**
     * A boolean indicating whether a space is usually inserted before.
     * This is the case for directives of type IN and POST.
     */
    public boolean addLeftSpace()
    {
      final DirectiveType in = DirectiveType.IN;
      final DirectiveType post = DirectiveType.POST;
      return getType().equals(in) || getType().equals(post);
    }

    /**
     * A boolean indicating whether a space is usually inserted after.
     * This is the case for directives of type IN and PRE.
     */
    public boolean addRightSpace()
    {
      final DirectiveType in = DirectiveType.IN;
      final DirectiveType pre = DirectiveType.PRE;
      return getType().equals(in) || getType().equals(pre);
    }

    public boolean equals(Object obj)
    {
      if (obj != null &&
          this.getClass().equals(obj.getClass())) {
        MarkupDirective directive = (MarkupDirective) obj;
        if (! command_.equals(directive.command_)) {
          return false;
        }
        if (! unicode_.equals(directive.unicode_)) {
          return false;
        }
        if (! type_.equals(directive.type_)) {
          return false;
        }
        if (! section_.equals(directive.section_)) {
          return false;
        }
        return true;
      }
      return false;
    }

    public String toString()
    {
      String result = command_ + "(" + type_ + ") --> " + unicode_ +
        " defined in " + section_;
      return result;
    }
  }
}
