/**
Copyright 2003 Mark Utting
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
package net.sourceforge.czt.z2b;

import java.util.*;
import java.util.logging.Logger;
import java.net.URL;

// the CZT classes for Z.
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

// the Gaffe plugins for analysing specs and schemas
import net.sourceforge.czt.animation.gui.generation.*;
import net.sourceforge.czt.animation.gui.generation.plugins.*;

// our classes
import net.sourceforge.czt.z2b.*;


/**
 * <p>This class converts a Z section into a B machine.
 *
 * @author Mark Utting
 */
public class Z2B
{
  // plugins for finding/classifying schemas and variables.
  private SchemaExtractor extractor;
  private SchemaIdentifier identify;
  private VariableExtractor varExtract;

  private ZFactory factory;

  private static final Logger sLogger
    = Logger.getLogger("net.sourceforge.czt.z2b");

  /**
   * Constructor for Z2B converter
   *
   * @param plugins Plugins to analyze the specification.
   * @param factory The object factory for making Z AST objects.
   */
  public Z2B(PluginList plugins, ZFactory factory)
    throws PluginInstantiationException {
    extractor = (SchemaExtractor)plugins.getPlugin(SchemaExtractor.class);
    identify = (SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class);
    varExtract = (VariableExtractor)plugins.getPlugin(VariableExtractor.class);
    this.factory = factory;
  }

  /** Translates a ZSect into a BMachine
   *  @param spec  the complete spec, which contains the ZSect
   *  @param sect  the ZSect to be translated
   *  @param url   the source location of the Z specification.
   *
   *  <esc> requires varExtract != null </esc>
   */
  public BMachine makeBMachine(Spec spec, ZSect sect, URL url)
    throws BException {
    List/*<ConstDecl<SchExpr>>*/ schemas;
    ConstDecl/*<SchExpr>*/ stateSchema;
    ConstDecl/*<SchExpr>*/ initSchema;
    List/*<ConstDecl<SchExpr>>*/ opSchemas;

    // find all the schemas 
    schemas = extractor.getSchemas(spec);

    // classify the schemas into state/init/operation.
    identify.identifySchemas(spec,schemas);
    stateSchema = identify.getStateSchema();
    initSchema = identify.getInitSchema();
    opSchemas = identify.getOperationSchemas();

    // Now check that the plugins have found the right schemas
    if (stateSchema == null)
	throw new BException("cannot find the state schema");
    Map svars = varExtract.getStateVariables(stateSchema);
    if (svars == null || svars.size() == 0)
	throw new BException("state schema contains no variables!");
    if ( ! (stateSchema.getExpr() instanceof SchExpr))
	throw new BException("state schema is not a simple schema");
    if (varExtract.getNumberedVariables(stateSchema).size() != 0
	|| varExtract.getInputVariables(stateSchema).size() != 0
	|| varExtract.getOutputVariables(stateSchema).size() != 0)
	throw new BException("state schema contains decorated variables");

    if (initSchema == null)
	throw new BException("cannot find the initialization schema");
    if (opSchemas == null || opSchemas.size() == 0)
	throw new BException("cannot find any operation schemas");

    // TODO: extend this extractor to handle x==E vars.
    //       Idea: return a map from DeclName to Expr (type)
    Pred invar = ((SchExpr)stateSchema.getExpr()).getSchText().getPred();

    BMachine mach = new BMachine(sect.getName(), url.toString());

    // Add state variables
    declareVars(svars, mach.getVariables(), mach.getInvariant());

    // add other invariant predicates
    addPred(invar, mach.getInvariant());

    // operations
    Iterator i = opSchemas.iterator();
    while (i.hasNext())
      mach.getOperations().add(operation((ConstDecl)i.next()));

    return mach;
  }

  /** Converts an expanded Z schema into a BOperation */
  protected BOperation operation(ConstDecl schema) {
    Map inputs = varExtract.getInputVariables(schema);
    Map outputs = varExtract.getOutputVariables(schema);
    String opName = schema.getDeclName().getWord();  // TODO: decorations?
    BOperation op = new BOperation(opName);
    declareVars(inputs, op.getInputs(), op.getPre());
    declareVars(outputs, op.getOutputs(), op.getPost());
    return op;
  }

  /** Adds a set of names and type constraints to names/preds lists */
  protected void declareVars(Map vars, List names, List preds) {
    Iterator v = vars.keySet().iterator();
    while (v.hasNext()) {
      DeclName n = (DeclName)v.next();
      VarDecl decl = (VarDecl)vars.get(n);
      names.add(n);
      preds.add(factory.createMemPred(refExpr(n),
				      decl.getExpr(),
				      Boolean.FALSE));
    }
  }

  /** Creates a RefExpr to a given DeclName */
  protected RefExpr refExpr(DeclName n) {
    RefName ref = factory.createRefName(n.getWord(), n.getStroke(), n);
    RefExpr e = factory.createRefExpr(ref, new ArrayList(), Boolean.FALSE);
    return e;
  }

  /** Flatten conjuncts and add them to the given list. */
  protected void addPred(Pred p, List preds) {
    if (p instanceof AndPred) {
      AndPred and = (AndPred)p;
      addPred(and.getLeftPred(), preds);
      addPred(and.getRightPred(), preds);
    }
    else {
      preds.add(p);
    }
  }
}

