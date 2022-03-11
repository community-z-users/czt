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

import net.sourceforge.czt.session.Dialect;

/**
 * This exception can be thrown by a markup converter.
 */
public class MarkupException
  extends Exception
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -2991741759209681172L;
  
  private final transient MarkupDirective directive1_;
  private final transient MarkupDirective directive2_;

  /**
   * Constructs a new exception with the specified detail message.
   */
  public MarkupException(MarkupDirective directive1,
                         MarkupDirective directive2)
  {
    super("LaTeX command " + (directive1 != null ? directive1.getCommand() : "null") +
          " defined twice " +
          "\n" + directive1 + "\n" + directive2);
    if (directive1 == null || directive2 == null) throw new NullPointerException(); 
    checkCompatibleDialects(directive1, directive2);
    directive1_ = directive1;
    directive2_ = directive2;
  }
  
  public MarkupException(MarkupDirective directive)
  {
	super("LaTeX command is ill-defined - some of its mandatory fields might be null or inconsistent: " 
			+ directive);
    if (directive == null) throw new NullPointerException(); 
	directive1_ = directive;
	directive2_ = null;
  }
  
  public Dialect getDialect()
  {
	  return directive1_.getDialect();
  }

  public MarkupDirective getMarkupDirective1()
  {
    return directive1_;
  }

  public MarkupDirective getMarkupDirective2()
  {
    return directive2_;
  }
  
  private void checkCompatibleDialects(MarkupDirective directive1,
          								MarkupDirective directive2)
  {
	  assert directive1 != null && directive2 != null;
	  if (!directive1.getDialect().equals(directive2.getDialect()) &&
		  (directive1.getDialect().isExtensionOf(directive2.getDialect()) ||
		  directive2.getDialect().isExtensionOf(directive1.getDialect())))
		  throw new IllegalArgumentException("Cannot create MarkupException for incompatible dialects: " + 
				  directive1.getDialect().toString() + " and " + directive2.getDialect().toString());
  }
}
