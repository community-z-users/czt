/*
  Copyright (C) 2004, 2005 Petra Malik
  Copyright (C) 2004 Mark Utting
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

package net.sourceforge.czt.session;

/**
 * The command interface provides a method for computing objects.
 * 
 * When the compute method is called, this command will try to compute
 * an object of the given name, and then insert it into the given
 * section manager.
 * 
 * For example, if name is "abc", then a parsing
 * command might try to read and parse a file called "abc.zed"
 * and then insert a Spec object into the section manager.
 */
public interface Command
{
  boolean compute(String name,
                  SectionManager manager)
    throws CommandException;
}
