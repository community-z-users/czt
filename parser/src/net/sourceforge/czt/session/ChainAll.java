/*
  Copyright (C) 2004 Petra Malik
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
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map;

/** This Chain of commands succeeds if every command returns true. */
public class ChainAll implements Chain
{
  protected List commands = new ArrayList();

  /**
   * Adds a command to the end of the chain.
   */
  public void add(Command cmd)
  { 
    commands.add(cmd);
  }

  public boolean execute(Context sectMan, Map args)
  throws Exception
  {
    boolean result = true;
    Iterator i = commands.iterator();
    while (result && i.hasNext())
      {
	Command cmd = (Command) i.next();
	result = sectMan.update(cmd,args);
      }
    return result;
  }
}

