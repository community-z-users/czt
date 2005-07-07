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

package net.sourceforge.czt.rules.codegen;

import java.io.FileWriter;
import java.io.Writer;
import java.util.Vector;

import org.apache.velocity.app.Velocity;
import org.apache.velocity.exception.ParseErrorException;
import org.apache.velocity.exception.ResourceNotFoundException;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.Template;

import org.apache.xerces.dom3.DOMConfiguration;
import org.apache.xerces.dom3.DOMError;
import org.apache.xerces.dom3.DOMErrorHandler;
import org.apache.xerces.dom3.bootstrap.DOMImplementationRegistry;
import org.apache.xerces.xs.*;

/**
 * @author Petra Malik
 */
public class Main
{
  private static String DEST_DIR = "build/";
  private static String PACKAGE_DIR = "src/net/sourceforge/czt/rules/ast/";
  private static String VM_DIR = "src/codegen/vm/";

  public static void main(String[] argv)
    throws Exception
  {
    System.setProperty(DOMImplementationRegistry.PROPERTY,
      "org.apache.xerces.dom.DOMXSImplementationSourceImpl");
    DOMImplementationRegistry registry =
      DOMImplementationRegistry.newInstance();
    XSImplementation impl =
      (XSImplementation) registry.getDOMImplementation("XS-Loader");
    XSLoader schemaLoader = impl.createXSLoader(null);
    DOMConfiguration config = schemaLoader.getConfig();
    DOMErrorHandler errorHandler = new ErrorHandler();
    config.setParameter("error-handler", errorHandler);
    config.setParameter("validate", Boolean.TRUE);
    XSModel model = schemaLoader.loadURI(argv[0]);
    Velocity.init();
    
    XSNamedMap map = model.getComponents(XSTypeDefinition.COMPLEX_TYPE);
    Vector jokers = new Vector();
    for (int i = 0; i < map.getLength(); i++) {
      XSComplexTypeDefinition item = (XSComplexTypeDefinition) map.item(i);
      String name = item.getName();
      if (name.startsWith("Joker") && ! name.endsWith("Binding") &&
          ! name.equals("Jokers")) {
        final JokerClass jokerClass = new JokerClass(item);
        jokers.add(jokerClass);
        VelocityContext context = new VelocityContext();
        context.put("joker", jokerClass);
        context.put("complex_type", item);
        context.put("isList", name.endsWith("List"));
        String dest = DEST_DIR + PACKAGE_DIR + "Prover" + name + ".java";
        write(dest, VM_DIR + "Joker.vm", context);
        dest = DEST_DIR + PACKAGE_DIR + "Prover" + name + "Binding.java";
        write(dest, VM_DIR + "Binding.vm", context);
      }
    }
    final String dest = DEST_DIR + PACKAGE_DIR + "ProverFactory.java";
    VelocityContext context = new VelocityContext();
    context.put("jokers", jokers);
    write(dest, VM_DIR + "Factory.vm", context);
  }

  private static void write(String destination,
                            String templateName,
                            VelocityContext context)
    throws Exception
  {
    Writer writer = new FileWriter(destination);
    Template template = Velocity.getTemplate(templateName);
    System.err.println("Writing file " + destination);
    template.merge(context, writer);
    writer.close();
  }
}

class ErrorHandler
  implements DOMErrorHandler
{
  public boolean handleError(DOMError error)
  {
    short severity = error.getSeverity();
    if (severity == DOMError.SEVERITY_ERROR) {
      System.err.println("[xs-error]: "+error.getMessage());
    }
    if (severity == DOMError.SEVERITY_WARNING) {
      System.err.println("[xs-warning]: "+error.getMessage());
    }
    return true;
  }
}
