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

package net.sourceforge.czt.ui;

import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.parser.zpatt.ParseUtils;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.jaxb.JaxbValidator;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.zpatt.ast.Rule;
import net.sourceforge.czt.zpatt.util.Rewrite;

public class RewriteEngine
{
  public static Term rewrite(Source astSource,
                             Source rulesSource,
                             SectionInfo sectInfo)
    throws Exception
  {
    Term ast = ParseUtils.parse(astSource, sectInfo);
    Term rules = ParseUtils.parse(rulesSource, sectInfo);
    return Rewrite.rewrite(ast, collectRules(rules));
  }

  public static List<Rule> collectRules(Term term)
  {
    List<Rule> result = new ArrayList();  
    if (term instanceof Spec) {
      for (Iterator i = ((Spec) term).getSect().iterator(); i.hasNext(); ) {
        Object sect = i.next();
        if (sect instanceof ZSect) {
          for (Iterator j = ((ZSect) sect).getPara().iterator(); j.hasNext(); ) {
            Object para = j.next();
            if (para instanceof Rule) {
              result.add((Rule) para);
            }
          }
        }
      }
    }
    return result;
  }

  public static void main(String[] args)
  {
    String usage = "Usage: rewrite"
      + " -in <inputfile> [ -out <outputfile>] -rule <rulefile>";
    try {
      String inputfile = null;
      String rulefile = null;
      OutputStream out = System.out;
      for (int i = 0; i < args.length; i++) {
        if ("-in".equals(args[i])) {
          if (++i < args.length) {
            inputfile = args[i];
          } else {
            System.err.println(usage);
            return;
          }
        } else if ("-out".equals(args[i])) {
          if (++i < args.length) {
            out = new FileOutputStream(args[i]);
          } else {
            System.err.println(usage);
            return;
          }
        } else if ("-rule".equals(args[i])) {
          if (++i < args.length) {
            rulefile = args[i];
          } else {
            System.err.println(usage);
            return;
          }
       } else {
          System.err.println(usage);
          return;
        }
      }
      Term term = rewrite(new FileSource(inputfile),
                          new FileSource(rulefile),
                          new SectionManager());
      if (term != null) {
        JaxbValidator validator = new JaxbValidator();
        if (! validator.validate(term)) {
          String message = "AST is not valid.";
        }
        JaxbXmlWriter xmlWriter = new JaxbXmlWriter();
        xmlWriter.write(term, out);
      }
      else {
        System.err.println("Parse error");
      }
      out.close();
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
}
