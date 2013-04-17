/*
 * ZEvesConsole.java
 * Copyright (C) 2008 Leo Freitas
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.jedit.zeves;

import java.io.StringWriter;

import org.gjt.sp.jedit.*;
import console.*;

import net.sourceforge.czt.zeves.*;

public class ZEvesConsole
  extends Shell
{
 
  //private ZEves zeves_;
  
  public ZEvesConsole()
  {
    super(ZEvesPlugin.NAME);    
    //zeves_ = new ZEves();
  }

  public void printInfoMessage(Output output)
  {
    output.print(null, ZEves.getBanner());
  }

  public void printPrompt(Console console, Output output)
  {
    String prompt = jEdit.getProperty("zeves.prompt");
    if (prompt != null) {
      output.writeAttrs(ConsolePane.colorAttributes(console.getInfoColor()), prompt);
      output.writeAttrs(null," ");
    }
  }

  public void execute(Console console, Output output, String command)
  {
    if (! command.equals("")) {
      //String parts[] = command.split(" ",2);
      StringWriter out = new StringWriter();      
      out.write(command);
      out.write("\n");
      //ui.setOutput(new PrintWriter(out));
      //ui.processCmd(parts[0], parts.length > 1 ? parts[1] : "");
      output.writeAttrs(null, out.toString());
    }
    output.commandDone();
  }

  public void execute(Console console, String input, Output output,
                      Output error, String command)
  {
    execute(console, output, command);
  }
}
