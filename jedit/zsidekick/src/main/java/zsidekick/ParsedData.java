/*
 * ParsedData.java
 * Copyright (C) 2006, 2007 Petra Malik
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
package zsidekick;

import org.gjt.sp.jedit.*;
import sidekick.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

public class ParsedData
  extends SideKickParsedData
{
  SectionManager manager_;
  Spec spec_;
  WffHighlight wffHighlight_;

  public ParsedData(String name)
  {
    super(name);
  }

  public void addData(Spec spec, SectionManager manager,
                      WffHighlight wffHighlight, Buffer buffer)
  {
    spec_ = spec;
    manager_ = manager;
    wffHighlight_ = wffHighlight;
    wffHighlight_.setSpec(spec);
    for (Sect sect : spec.getSect()) {
      root.add(new CztTreeNode(sect, buffer));
    }
  }

  public Spec getSpec()
  {
    return spec_;
  }

  public SectionManager getManager()
  {
    return manager_;
  }
}
