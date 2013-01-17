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

/**
 * This exception can be thrown by a markup converter.
 */
public class MarkupException
  extends Exception
{
  private MarkupDirective directive1_;
  private MarkupDirective directive2_;

  /**
   * Constructs a new exception with the specified detail message.
   */
  public MarkupException(MarkupDirective directive1,
                         MarkupDirective directive2)
  {
    super("LaTeX command " + directive1.getCommand() +
          " defined twice " +
          "\n" + directive1 + "\n" + directive2);
    directive1_ = directive1;
    directive2_ = directive2;
  }
  
  public MarkupException(MarkupDirective directive)
  {
	super("LaTeX command is ill-defined - some of its mandatory fields might be null or inconsistent: " 
			+ directive);
	directive1_ = directive;
	directive2_ = null;
  }

  public MarkupDirective getMarkupDirective1()
  {
    return directive1_;
  }

  public MarkupDirective getMarkupDirective2()
  {
    return directive2_;
  }
}
