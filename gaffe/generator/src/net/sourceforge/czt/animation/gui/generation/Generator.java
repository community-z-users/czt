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
package net.sourceforge.czt.animation.gui.generation;

import java.io.OutputStream;

import java.net.URL;

import java.util.Arrays;
import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.animation.gui.generation.plugins.*;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.*;
 
import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.DeclName;

/**
 * The main program of the GAfFE Generator.
 * Joins together the various {@link net.sourceforge.czt.animation.gui.generation.plugins plugins} that make
 * the generator.
 * @author Nicholas Daley
 * @see net.sourceforge.czt.animation.gui.generation.plugins
 */
public final class Generator {
  /**
   * The collection of plugins/plugin types used by the generator.
   * @see net.sourceforge.czt.animation.gui.generation.plugins
   * @see PluginList
   */
  private static PluginList plugins
  =new PluginList(new Class[] {SpecSource.class,                  SchemaExtractor.class,
			       SchemaIdentifier.class,            VariableExtractor.class, 
			       DOMBeanChooser.class/*,              DOMInterfaceGenerator.class*/,
                               InterfaceDestination.class},
		  new Class[] {SpecReaderSource.class,            VisitorSchemaExtractor.class,
			       CommandLineSchemaIdentifier.class, DefaultVariableExtractor.class,
			       BasicDOMBeanChooser.class/*,         BasicInterfaceGenerator.class*/,
			       FileInterfaceDestination.class},
		  "Generator",
		  "Generates a (.gaffe) interface file from a (.zml) Z specification.");
  

  /** 
   * The Generator's main method.
   * Has @{link #plugins plugins} process the command line options, then feeds the data between the various
   * plugins.
   */
  public static void main(String[] args) {
    plugins.processOptions(args);
    
    Term specification=((SpecSource)plugins.getPlugin(SpecSource.class)).obtainSpec();
    URL specsURL=((SpecSource)plugins.getPlugin(SpecSource.class)).getURL();
    List/*<ConstDecl<SchExpr>>*/ schemas
      =((SchemaExtractor)plugins.getPlugin(SchemaExtractor.class)).getSchemas(specification);
    ((SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class)).identifySchemas(specification,schemas);
    ConstDecl/*<SchExpr>*/ stateSchema
      =((SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class)).getStateSchema();
    ConstDecl/*<SchExpr>*/ initSchema
      =((SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class)).getInitSchema();
    List/*<ConstDecl<SchExpr>>*/ operationSchemas
      =((SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class)).getOperationSchemas();
    OutputStream out
      =((InterfaceDestination)plugins.getPlugin(InterfaceDestination.class)).obtainOutputStream(specsURL);
    ((DOMInterfaceGenerator)plugins.getPlugin(DOMInterfaceGenerator.class))
      .generateInterface(specification, schemas, stateSchema, initSchema, operationSchemas, 
			 ((VariableExtractor)plugins.getPlugin(VariableExtractor.class)),
			 ((DOMBeanChooser)plugins.getPlugin(DOMBeanChooser.class)),
			 out);
  };
};
