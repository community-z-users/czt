/*
 * CommunityZToolsPlugin.java
 * Copyright (C) 2004 Petra Malik
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

import java.util.Vector;

import org.gjt.sp.jedit.*;
import errorlist.*;


public class CommunityZToolsPlugin extends EditPlugin
{
  protected static final DefaultErrorSource errorSource_ =
    new DefaultErrorSource("CZT");

  public void start()
  {
    ErrorSource.registerErrorSource(errorSource_);
  }

  public void stop()
  {
    ErrorSource.unregisterErrorSource(errorSource_);
  }
}
