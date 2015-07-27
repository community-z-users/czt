/*
  Copyright 2004, 2007 Petra Malik
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

package net.sourceforge.czt.parser.util;

import java.math.BigInteger;

import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.DirectiveType;
import net.sourceforge.czt.z.ast.LocAnn;

public class MarkupDirective
{
  private final String command_;
  private final String unicode_;
  private final DirectiveType type_;
  private final String section_;
  private final BigInteger lineNr_;
  
  private final Dialect dialect_;

  /**
   * @throws NullPointerException if one of the arguments
   *         is <code>null</code>.
   */
  public MarkupDirective(Dialect dialect, 
		  				 String command,
                         String unicode,
                         DirectiveType type,
                         String section,
                         BigInteger lineNr)
  	throws MarkupException
  {
    if (dialect == null) throw new NullPointerException();
    command_ = command;
    unicode_ = unicode;
    type_ = type;
    section_ = section;
    lineNr_ = lineNr;
    dialect_ = dialect;
    checkMembersNonNull();
  }

  /**
   * @throws NullPointerException if <code>directive</code> or
   *         <code>section</code> is <code>null</code>; or if
   *         the command, unicode, or type of the given directive
   *         is <code>null</code>.
   */
  public MarkupDirective(Dialect dialect, Directive directive, String section)
  	throws MarkupException
  {
	if (directive == null || dialect == null) throw new NullPointerException();
    command_ = directive.getCommand();
    unicode_ = directive.getUnicode();
    type_ = directive.getDirectiveType();
    section_ = section;
    dialect_ = dialect;
    LocAnn locAnn = directive.getAnn(LocAnn.class);
    if (locAnn != null) {
      lineNr_ = locAnn.getLine();
    }
    else
      lineNr_ = null;
    checkMembersNonNull();
  }

  /**
   * Throws a <code>NullPointerException</code> if one of the member
   * variables is <code>null</code>.
   */
  private void checkMembersNonNull() throws MarkupException
  {
    if (command_ == null || unicode_ == null ||
        type_ == null || section_ == null) {
      throw new MarkupException(this);
    }
  }
  
  public Dialect getDialect()
  {
	return dialect_;
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
  
  public int hashCode()
  {
	  int h = super.hashCode();
	  h += command_.hashCode();
	  h += unicode_.hashCode();
	  h += type_.hashCode();
	  h += section_.hashCode();
	  return h;
  }

  public String toString()
  {
    String result = command_ + "(" + type_ + ") --> " + unicode_ +
      " defined in " + section_ + " at line " + lineNr_;
    return result;
  }
}
