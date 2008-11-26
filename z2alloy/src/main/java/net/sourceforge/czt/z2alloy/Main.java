/**
Copyright 2008 Petra Malik
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.z2alloy;

import java.io.*;
import java.util.logging.*;
import java.util.*;
import java.net.URL;

import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

/** Translate a Z specification from ZML format into B format.
 *
 *  It takes a file spec.xml and produces a file spec.mch.
 */
public class Main
{
  public static void main(String[] args)
    throws Exception
  {
    Logger logger = Logger.getLogger("");
    for (Handler h : logger.getHandlers()) {
      h.setLevel(Level.SEVERE);
    }
    // Now read the spec 
    if (args.length < 1) {
      System.err.println("Args: spec.tex");
      System.exit(1);
    }
    final String input = args[0];
    File file = new File(input);
    FileSource source = new FileSource(input);
    SectionManager manager = new SectionManager("zpatt");
    String name = "spec";
    manager.put(new Key(name, Source.class), source);
    Spec spec = (Spec) manager.get(new Key(name, Spec.class));


    // now create the output file
    // choose the section -- we just take the last one!
    ZSect sect;
    List sects = spec.getSect();
    if (sects.size() > 0 && sects.get(sects.size()-1) instanceof ZSect) {
      sect = (ZSect) spec.getSect().get(sects.size()-1);
    }
    else {
      throw new Exception("last section is not a ZSect");
    }
    manager.get(new Key(sect.getName(), SectTypeEnvAnn.class)); // typecheck

    Z2Alloy foo = new Z2Alloy(manager);
    sect.accept(foo);
  }
}
