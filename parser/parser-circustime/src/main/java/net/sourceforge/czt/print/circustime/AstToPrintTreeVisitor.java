/*
  Copyright (C) 2006 Leo Freitas
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

package net.sourceforge.czt.print.circustime;

import net.sourceforge.czt.session.SectionInfo;

/**
 * TODO: add Circus time precedences (see the Z one for how it's done).
 */
public class AstToPrintTreeVisitor
  extends net.sourceforge.czt.print.circus.AstToPrintTreeVisitor
  
{
  /**
   * Creates a new ast to print tree visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public AstToPrintTreeVisitor(SectionInfo sectInfo, WarningManager wm)
  {
    super(sectInfo, wm);
  }
  
  protected WarningManager getWM()
  {
    return (WarningManager)warningManager_;
  }

}
