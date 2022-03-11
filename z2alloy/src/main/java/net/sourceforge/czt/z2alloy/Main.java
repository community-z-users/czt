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

import java.io.File;
import java.util.List;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z2alloy.ast.Func;
import net.sourceforge.czt.z2alloy.ast.Sig;

/** Translate a Z specification from ZML format into B format.
 *
 *  It takes a file spec.xml and produces a file spec.mch.
 */
public class Main
{

  /**
   * parses, translates, and prints to System.out the resulting alloy model
   */
  public static void main(String[] args)
  throws Exception
  {
    Logger logger = Logger.getLogger("");
    for (Handler h : logger.getHandlers()) {
      h.setLevel(Level.SEVERE);
    }

    boolean unfolding = false;
    String input = null;
    for (int i = 0; i < args.length; i++) {
      if ("-h".equals(args[i]) ||
          "-help".equals(args[i]) ||
          "--help".equals(args[i])) {
        System.err.println(usage());
        return;
      }
      if ("-u".equals(args[i]) ||
          "-unfolding".equals(args[i])) {
        unfolding = true;
      }
      else {
        input = args[i];
      }
    }
    if (input == null) {
      System.err.println(usage());
      System.exit(1);
    }

    Z2Alloy foo = translate(new File(input), unfolding);
    System.out.println(print(foo));

  }

  /**
   * uses AlloyPrinter to create a string of the whole model.
   * 
   * this string should generally be parsable by the alloy analyser
   */

  public static String print (Z2Alloy model) {
    String ret = "open util/integer\n\n";
    AlloyPrinter p = new AlloyPrinter();

    for (Object element : model.module()) {
      if (element instanceof Sig) {
        ret += p.visitSig((Sig) element) + "\n\n";
      }
      else if (element instanceof Func) {
        ret += p.print((Func) element) + "\n\n";
      }
    }      
    return ret;
  }

  /**
   * translates the input into a Z2Alloy model
   */
  public static Z2Alloy translate (File input, boolean unfolding) throws Exception {
    FileSource source = new FileSource(input);
    SectionManager manager = new SectionManager(Dialect.ZPATT);
    String name = "spec";
    manager.put(new Key<Source>(name, Source.class), source);
    Spec spec = manager.get(new Key<Spec>(name, Spec.class));


    // now create the output file
    // choose the section -- we just take the last one!
    ZSect sect;
    List<Sect> sects = spec.getSect();
    if (sects.size() > 0 && sects.get(sects.size()-1) instanceof ZSect) {
      sect = (ZSect) spec.getSect().get(sects.size()-1);
    }
    else {
      throw new Exception("last section is not a ZSect");
    }
    manager.get(new Key<SectTypeEnvAnn>(sect.getName(), SectTypeEnvAnn.class)); // typecheck

    Z2Alloy foo = Z2Alloy.setInstance(manager);
    foo.setUnfolding(unfolding);
    sect.accept(foo);
    return foo;

  }

  /**
   * TODO: needs updating!
   */
  public static String usage()
  {
    return "Args: spec.tex";
  }
}
