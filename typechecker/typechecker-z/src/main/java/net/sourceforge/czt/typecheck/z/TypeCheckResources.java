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

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Map;
import java.util.ListResourceBundle;
import java.util.Properties;

import net.sourceforge.czt.util.CztLogger;

public class TypeCheckResources
  extends ListResourceBundle
{
  protected static final String MESSAGES =
    "/net/sourceforge/czt/typecheck/z/ErrorMessage_en.properties";

  //the contents are represented in two formats to make it easy for
  //typecheckers that build on this to add and override error messages
  final static Properties properties_ = new Properties();
  static Object [][] contents_;

  static {
    addFile(TypeCheckResources.class.getResource(MESSAGES));
  }

  protected static void addFile(URL file)
  {
    try {
      InputStream urlStream = file.openStream();
      try {
        properties_.load(urlStream);
      } finally {
        urlStream.close();
      }
    }
    catch (IOException exception) {
      String message = "Cannot open properties file " + file;
      CztLogger.getLogger(TypeCheckResources.class).warning(message);
    }

    contents_ = new Object [properties_.size()][2];
    java.util.Set<Map.Entry<Object, Object>> set = properties_.entrySet();
    int i = 0;
    for (Map.Entry<?, ?> next : set) {
      contents_[i][0] = next.getKey();
      contents_[i++][1] = next.getValue();
    }
  }

  public Object[][] getContents()
  {
    return contents_.clone();
  }
}

