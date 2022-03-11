/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley
 
 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.
 
 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.animation.gui.generation.plugins.impl;

import java.io.File;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * Visitor class for finding all of the schemas in a Z specification.
 * @author Nicholas Daley
 */
final class SchemaExtractionVisitor
    implements
      SpecVisitor<Object>,
      ZSectVisitor<Object>,
      AxParaVisitor<Object>,
      ConstDeclVisitor<Object>
{
  /**
   * The list of collected schemas.
   */
  private Vector<ConstDecl> schemas = null;

  /**
   * Getter method for <tt>schemas</tt>.
   */
  public List<ConstDecl> getSchemas(Term term)
  {
    schemas = new Vector<ConstDecl>();
    term.accept(this);
    return new Vector<ConstDecl>(schemas);
  };

  /**
   * Method for visiting all of the members of a list.
   */
  private void visitAllOf(List list, Class clazz)
  {
    for (Iterator it = list.iterator(); it.hasNext();) {
      Object item = it.next();
      if (item != null && clazz.isInstance(item))
        if (item instanceof Term)
          ((Term) item).accept(this);
    }
  };

  /**
   * Visitor method for finding the schemas in a specification.
   */
  public Object visitSpec(Spec zedObject)
  {
    visitAllOf(zedObject.getSect(), ZSect.class);
    return null;
  };//Only interested in ZSects

  /**
   * Visitor method for finding the schemas in a section.
   */
  public Object visitZSect(ZSect zedObject)
  {
    visitAllOf(ZUtils.assertZParaList(zedObject.getParaList()), AxPara.class);
    return null;
  };//Containing AxParas

  /**
   * Visitor method for finding the schemas in an <tt>AxPara</tt>.
   */
  public Object visitAxPara(AxPara zedObject)
  {//Only interested in AxParas
    visitAllOf(zedObject.getZSchText().getZDeclList(), ConstDecl.class);
    return null;
  };//Containing ConstDecls

  /**
   * Visitor method for identifying if a <tt>ConstDecl</tt> is a schema.
   */
  public Object visitConstDecl(ConstDecl zedObject)
  {//Only interested in ConstDecls with RHS=SchExpr
    if (zedObject.getExpr() instanceof SchExpr)
      schemas.add(zedObject);
    return null;
  };

  /**
   * main method for testing.
   */
  public static void main(String[] args)
  {
    if (args.length != 1) {
      System.err.println("Requires one argument - specification file.");
      return;
    }

    JaxbXmlReader reader = new JaxbXmlReader();
    Term term = reader.read(new File(args[0]));

    SchemaExtractionVisitor extracter = new SchemaExtractionVisitor();
    List schemas = extracter.getSchemas(term);
    for (Iterator it = schemas.iterator(); it.hasNext();) {
      ConstDecl schema = (ConstDecl) it.next();
      DeclName declName = schema.getDeclName();
      //SchExpr schExpr=(SchExpr)schema.getExpr();
      System.err.println("Schema " + declName.toString());
    };
  };
};
