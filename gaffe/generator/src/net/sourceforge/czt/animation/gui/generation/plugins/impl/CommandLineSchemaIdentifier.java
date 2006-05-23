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

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.animation.gui.generation.BadOptionException;
import net.sourceforge.czt.animation.gui.generation.Option;
import net.sourceforge.czt.animation.gui.generation.OptionHandler;
import net.sourceforge.czt.animation.gui.generation.plugins.SchemaIdentifier;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ConstDecl;

/**
 * Plugin implementation for identifying the purpose of schemas.
 * A list of schemas is fed into this plugin.  After which it can be queried for the state schema, init 
 * schema, and operation schemas.
 * @author Nicholas Daley
 */
public final class CommandLineSchemaIdentifier implements SchemaIdentifier
{
  /**
   * {@inheritDoc}
   * Options are used for identifying state, init, and operation schemas.
   * <ul>
   *   <li>-initSchema &lt;schema name&gt;</li>
   *   <li>-stateSchema &lt;schema name&gt;</li>
   *   <li>-opSchema &lt;schema name&gt;</li>
   * </ul>
   */
  public Option[] getOptions()
  {
    return new Option[]{
        new Option("initSchema", Option.MUST, "schema name",
            "Name of the initialisation schema to use.", initHandler),
        new Option("stateSchema", Option.MUST, "schema name",
            "Name of the state schema to use.", stateHandler),
        new Option("opSchema", Option.MUST, "schema name",
            "Name of an operation schema to use.", opHandler),
        new Option(doneHandler)};
  };

  /**
   * {@inheritDoc}
   */
  public String getHelp()
  {
    return "Identifies state, initialisation, and operation schemas.";
  };

  /**
   * Name of initialisation schema passed in by <tt>-initSchema</tt>.
   */
  private String initSchemaName = null;

  /**
   * Name of state schema passed in by <tt>-stateSchema</tt>.
   */
  private String stateSchemaName = null;

  /**
   * Names of operation schemas passed in (one at a time) by <tt>-opSchema</tt>.
   */
  private HashSet<String> operationSchemaNames = new HashSet<String>();

  /**
   * Handler for setting {@link #initSchemaName initSchemaName}.
   */
  private final OptionHandler initHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
    {
      initSchemaName = argument;
    };
  };

  /**
   * Handler for setting {@link #stateSchemaName stateSchemaName}.
   */
  private final OptionHandler stateHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
    {
      stateSchemaName = argument;
    };
  };

  /**
   * Handler for setting {@link #operationSchemaNames operationSchemaNames}.
   */
  private final OptionHandler opHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
    {
      operationSchemaNames.add(argument);
    };
  };

  /**
   * Handler for the end of option processing.
   */
  private final OptionHandler doneHandler = new OptionHandler()
  {
    public void handleOption(Option opt, String argument)
        throws BadOptionException
    {
      if (stateSchemaName == null)
        throw new BadOptionException(
            "The CommandLineSchemaIdentifier needs an option giving a name for "
                + "the state schema.");
    };
  };

  /**
   * The state schema found in the specification.
   */
  private ConstDecl/*<SchExpr>*/stateSchema = null;

  /**
   * The initialisation schema found in the specification.
   */
  private ConstDecl/*<SchExpr>*/initSchema = null;

  /**
   * The operation schemas found in the specification.
   */
  private List<ConstDecl/*<SchExpr>*/> operationSchemas = new Vector<ConstDecl/*<SchExpr>*/>();

  /**
   * Getter method for stateSchema.
   */
  public ConstDecl/*<SchExpr>*/getStateSchema()
  {
    return stateSchema;
  };

  /**
   * Getter method for initSchema.
   */
  public ConstDecl/*<SchExpr>*/getInitSchema()
  {
    return initSchema;
  };

  /**
   * Getter method for operationSchemas.
   */
  public List<ConstDecl/*<SchExpr>*/> getOperationSchemas()
  {
    return operationSchemas;
  };

  /**
   * Method for feeding in the list of schemas to identify.
   * @param specification Term containing the Spec, Sect, or Para 
   *        the schemas were found in. 
   * @param schemas The list of schemas.
   * @throws IllegalStateException if it has not been given enough 
   *         information (e.g. from the command line) to determine this.
   */
  public void identifySchemas(Term specification,
      List<ConstDecl/*<SchExpr>*/> schemas) throws IllegalStateException
  {
    String me = "The CommandLineSchemaIdentifier ";
    if (stateSchemaName == null) //Should have been handled by 
      throw new Error("Option processing must be done before "
          + "CommandLineSchemaIdentifier.identifySchemas is " + "called.");
    if (initSchemaName == null)
      initSchemaName = "Init" + stateSchemaName;

    for (Iterator it = schemas.iterator(); it.hasNext();) {
      ConstDecl/*<SchExpr>*/schema = (ConstDecl/*<SchExpr>*/) it.next();
      String schemaName = schema.getDeclName().toString();
      if (schemaName.equals(initSchemaName))
        initSchema = schema;
      if (schemaName.equals(stateSchemaName))
        stateSchema = schema;
      if (operationSchemaNames.contains(schemaName)) {
        operationSchemas.add(schema);
        operationSchemaNames.remove(schemaName);
      }
    }
    if (initSchema == null)
      throw new IllegalStateException(me + "could not find an init schema.");
    if (stateSchema == null)
      throw new IllegalStateException(me + "could not find a state schema.");

    if (!operationSchemaNames.isEmpty())
      throw new IllegalStateException(me + "could not find a schema called: "
          + operationSchemaNames.iterator().next());
  };
};
