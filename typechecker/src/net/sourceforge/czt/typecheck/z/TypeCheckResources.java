/*
  Copyright (C) 2005 Petra Malik
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

package net.sourceforge.czt.typecheck.z;

import java.util.ListResourceBundle;
import java.util.Properties;

import net.sourceforge.czt.util.CztLogger;

public class TypeCheckResources
  extends ListResourceBundle
{
  private static final String MESSAGES =
    "/net/sourceforge/czt/typecheck/z/ErrorMessage_en.properties";
  private static final Object[][] contents_ = computeContents();

  private static Object[][] computeContents()
  {
    final Properties msgProps = new Properties();
    try {
      msgProps.load(TypeCheckResources.class.getResourceAsStream(MESSAGES));
    }
    catch (Exception exception) {
      String message = "Cannot open properties file " + MESSAGES;
      CztLogger.getLogger(TypeCheckResources.class).warning(message);
    }
    final Object[] msgValues = ErrorMessage.values();
    Object[][] result = new Object[msgValues.length][2];
    for (int i = 0; i < msgValues.length; i++) {
      final String msg = msgValues[i].toString();
      assert msg != null;
      String msgValue = msgProps.getProperty(msg);
      if (msgValue == null) {
        msgValue = msg;
      }
      result[i][0] = msg;
      result[i][1] = msgValue;
    }
    return result;
  }

  public Object[][] getContents()
  {
    return contents_;
  }
}

