/**
Copyright 2003 Mark Utting
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

import net.sourceforge.czt.core.ast.*;
import net.sourceforge.czt.core.impl.*;
import net.sourceforge.czt.util.DebugProxy;

/**
 * An object factory which creates an debug proxy for DeclName objects.
 * Whenever a DeclName is created, this object factory wraps a debug
 * proxy around it and returns the proxy instead.
 */
public class DebugFactory
  extends CoreFactoryImpl
{
  public DeclName createDeclName()
  {
    DeclName orig = super.createDeclName();
    return (DeclName) DebugProxy.newInstance(orig);
  }
}
