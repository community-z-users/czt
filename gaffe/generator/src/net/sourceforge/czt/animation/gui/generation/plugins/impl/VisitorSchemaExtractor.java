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

import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.plugins.SchemaExtractor;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ConstDecl;

/**
 * Plugin implementation for finding all of the schemas in a specification.
 * Uses {@link SchemaExtractionVisitor SchemaExtractionVisitor}.
 @author Nicholas Daley
 */
public final class VisitorSchemaExtractor implements SchemaExtractor
{
  /** 
   * {@inheritDoc}
   * VisitorSchemaExtractor takes no options.
   */
  public Option[] getOptions()
  {
    return new Option[]{};
  };

  /**
   * {@inheritDoc}
   */
  public String getHelp()
  {
    return "Finds the schemas in the Z specification.";
  };

  /**
   * The visitor to be used to find the schemas.
   */
  private SchemaExtractionVisitor visitor = new SchemaExtractionVisitor();

  /**
   * {@inheritDoc}
   * Uses SchemaExtractionVisitor#getSchemas(Term)
   */
  public List<ConstDecl/*<SchExpr>*/> getSchemas(Term spec)
  {
    List<ConstDecl/*<SchExpr>*/> vs = visitor.getSchemas(spec);
    System.out.println("Schemas:");
    for (Iterator it = vs.iterator(); it.hasNext();)
      System.out.println(((ConstDecl) it.next()).getDeclName().toString());

    return vs;
  };
};
