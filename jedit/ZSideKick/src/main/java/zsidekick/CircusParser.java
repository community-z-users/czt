/*
 * CircusParser.java
 * Copyright (C) 2006 Leo Freitas
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

import net.sourceforge.czt.session.*;

public class CircusParser
  extends AbstractParser
{
  public CircusParser()
  {
    super("circus");
  }

  public SectionManager getManager()
  {
    SectionManager manager = new SectionManager("circus");
    setParseProperties(manager);
    return manager;
  }

  public Markup getMarkup()
  {
    return Markup.UNICODE;
  }
}
