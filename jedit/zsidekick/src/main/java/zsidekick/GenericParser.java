/*
 * GenericParser.java
 * Copyright (C) 2006 Petra Malik
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

import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;

public class GenericParser
  extends AbstractParser
{
  private String extension_;
  private Markup markup_;

  public GenericParser(String extension, Markup markup)
  {
    super(extension + markup);
    extension_ = extension;
    markup_ = markup;
  }

  public SectionManager getManager()
  {
    SectionManager manager = new SectionManager(extension_);
    setParseProperties(manager);
    return manager;
  }

  public Markup getMarkup()
  {
    return markup_;
  }
}
