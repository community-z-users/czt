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

import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.net.URL;
import java.util.List;

import net.sourceforge.czt.animation.gui.generation.plugins.BeanChooser;
import net.sourceforge.czt.animation.gui.generation.plugins.BeanInterfaceGenerator;
import net.sourceforge.czt.animation.gui.generation.plugins.InterfaceDestination;
import net.sourceforge.czt.animation.gui.generation.plugins.SchemaExtractor;
import net.sourceforge.czt.animation.gui.generation.plugins.SchemaIdentifier;
import net.sourceforge.czt.animation.gui.generation.plugins.SpecSource;
import net.sourceforge.czt.animation.gui.generation.plugins.VariableExtractor;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.BasicBeanChooser;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.BasicBeanInterfaceGenerator;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.CommandLineSchemaIdentifier;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.DefaultVariableExtractor;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.FileInterfaceDestination;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.SpecReaderSource;
import net.sourceforge.czt.animation.gui.generation.plugins.impl.VisitorSchemaExtractor;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.z.ast.ConstDecl;

import org.apache.bsf.BSFException;
import org.apache.bsf.BSFManager;
import org.apache.bsf.util.IOUtils;

/**
 * The main program of the GAfFE Generator.
 * Joins together the various {@link net.sourceforge.czt.animation.gui.generation.plugins plugins} that make
 * the generator.
 * @author Nicholas Daley
 * @see net.sourceforge.czt.animation.gui.generation.plugins
 */
public final class Generator
{
  /**
   * The collection of plugins/plugin types used by the generator.
   * @see net.sourceforge.czt.animation.gui.generation.plugins
   * @see PluginList
   */
  private static PluginList plugins = new PluginList(/*(Class<Plugin>[]) Array.newInstance(Plugin.class, 7)*/

  (Class<Plugin>[]) new Class[]{SpecSource.class, SchemaExtractor.class,
      SchemaIdentifier.class, VariableExtractor.class, BeanChooser.class,
      BeanInterfaceGenerator.class, InterfaceDestination.class},
      (Class<Plugin>[]) new Class[]{SpecReaderSource.class,
          VisitorSchemaExtractor.class, CommandLineSchemaIdentifier.class,
          DefaultVariableExtractor.class, BasicBeanChooser.class,
          BasicBeanInterfaceGenerator.class, FileInterfaceDestination.class},
      "Generator",
      "Generates a (.gaffe) interface file from a (.zml) Z specification.");

  /** 
   * The Generator's main method.
   * Has @{link #plugins plugins} process the command line options, then feeds the data between the various
   * plugins.
   */
  public static void main(String[] args)
  {
    try {
      plugins.processOptions(args);
      SpecSource specSource;
      SchemaExtractor schemaExtractor;
      SchemaIdentifier schemaIdentifier;
      InterfaceDestination interfaceDestination;
      BeanInterfaceGenerator interfaceGenerator;
      VariableExtractor variableExtractor;
      BeanChooser beanChooser;
      try {
        specSource = (SpecSource) plugins.getPlugin(SpecSource.class);
        schemaExtractor = (SchemaExtractor) plugins
            .getPlugin(SchemaExtractor.class);
        schemaIdentifier = (SchemaIdentifier) plugins
            .getPlugin(SchemaIdentifier.class);
        interfaceDestination = (InterfaceDestination) plugins
            .getPlugin(InterfaceDestination.class);
        interfaceGenerator = (BeanInterfaceGenerator) plugins
            .getPlugin(BeanInterfaceGenerator.class);
        variableExtractor = (VariableExtractor) plugins
            .getPlugin(VariableExtractor.class);
        beanChooser = (BeanChooser) plugins.getPlugin(BeanChooser.class);
      } catch (PluginInstantiationException ex) {
        throw new BadOptionException(ex);
      }
      Term specification;
      try {
        specification = specSource.obtainSpec();
      } catch (IllegalStateException ex) {
        throw new BadOptionException(ex);
      } catch (CommandException ex) {
        System.err.println(ex);
        return;
      }

      URL specsURL = specSource.getURL();
      List<ConstDecl/*<SchExpr>*/> schemas = schemaExtractor
          .getSchemas(specification);

      try {
        schemaIdentifier.identifySchemas(specification, schemas);
      } catch (IllegalStateException ex) {
        throw new BadOptionException(ex);
      };

      ConstDecl/*<SchExpr>*/stateSchema = schemaIdentifier.getStateSchema();
      ConstDecl/*<SchExpr>*/initSchema = schemaIdentifier.getInitSchema();

      List<ConstDecl/*<SchExpr>*/> operationSchemas = schemaIdentifier
          .getOperationSchemas();

      OutputStream out;
      try {
        out = interfaceDestination.obtainOutputStream(specsURL);
      } catch (IllegalStateException ex) {
        throw new BadOptionException(ex);
      };

      runConfigScripts();

      interfaceGenerator.generateInterface(specification, specsURL, schemas,
          stateSchema, initSchema, operationSchemas, variableExtractor,
          beanChooser, out);
    } catch (BadOptionException ex) {
      System.err.println(ex);
      System.err.println();
      System.err.println("Run \"Generator -help\" for help.");
      return;
    };
  };

  protected static void runConfigScripts()
  {
    BSFManager bsfm = new BSFManager();
    try {
      bsfm.declareBean("err", System.err, System.err.getClass());
      bsfm.declareBean("out", System.out, System.out.getClass());
    } catch (BSFException ex) {
      throw new Error(
          "Beans couldn't be declared for the configuration script." + ex);
    }
    String scriptName = "net/sourceforge/czt/animation/gui/persistence/persistence-config.js";
    InputStreamReader in = new InputStreamReader(ClassLoader
        .getSystemResourceAsStream(scriptName));
    try {
      bsfm
          .exec("javascript", scriptName, 1, 0, IOUtils.getStringFromReader(in));
    } catch (IOException ex) {
      throw new Error(
          "Couldn't read the persistence config script from the package.");
    } catch (BSFException ex) {
      System.err
          .println("Warning: Caught exception caused by the persistence config script."
              + ex);
    }
  };
};
