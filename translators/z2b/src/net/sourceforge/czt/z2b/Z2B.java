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
  implements TermVisitor,
             GivenParaVisitor,
	     FreetypeVisitor,
	     AxParaVisitor,
	     ConjParaVisitor,
	     NarrParaVisitor,
	     OptempParaVisitor,
	     UnparsedParaVisitor
{
  // plugins for finding/classifying schemas and variables.
  private SchemaExtractor extractor_;
  private SchemaIdentifier identify_;
  private VariableExtractor varExtract_;

  private BMachine mach_ = null;

  private static final Logger sLogger
    = Logger.getLogger("net.sourceforge.czt.z2b");

  /**
   * Constructor for Z2B converter
   *
   * @param plugins Plugins to analyze the specification.
   */
  public Z2B(PluginList plugins)
    throws PluginInstantiationException {
    extractor_ = (SchemaExtractor)plugins.getPlugin(SchemaExtractor.class);
    identify_ = (SchemaIdentifier)plugins.getPlugin(SchemaIdentifier.class);
    varExtract_ =(VariableExtractor)plugins.getPlugin(VariableExtractor.class);
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
    schemas = extractor_.getSchemas(spec);

    // classify the schemas into state/init/operation.
    identify_.identifySchemas(spec,schemas);
    stateSchema = identify_.getStateSchema();
    initSchema = identify_.getInitSchema();
    opSchemas = identify_.getOperationSchemas();

    // Now check that the plugins have found the right schemas
    if (stateSchema == null)
	throw new BException("cannot find the state schema");
    Map svars = varExtract_.getStateVariables(stateSchema);
    if (svars == null || svars.size() == 0)
	throw new BException("state schema contains no variables!");
    if ( ! (stateSchema.getExpr() instanceof SchExpr))
	throw new BException("state schema is not a simple schema");
    if (varExtract_.getNumberedVariables(stateSchema).size() != 0
	|| varExtract_.getInputVariables(stateSchema).size() != 0
	|| varExtract_.getOutputVariables(stateSchema).size() != 0)
	throw new BException("state schema contains decorated variables");

    if (initSchema == null)
	throw new BException("cannot find the initialization schema");
    if (opSchemas == null || opSchemas.size() == 0)
	throw new BException("cannot find any operation schemas");

    // TODO: extend this extractor to handle x==E vars.
    //       Idea: return a map from DeclName to Expr (type)
    Pred invar = ((SchExpr)stateSchema.getExpr()).getSchText().getPred();

    mach_ = new BMachine(sect.getName(), url.toString());

    // Process all the non-schema definitions from sect
    VisitorUtils.visitList(this, sect.getPara());
    
    // Add state variables
    declareVars(svars, mach_.getVariables(), mach_.getInvariant());

    // add other invariant predicates
    addPred(invar, mach_.getInvariant());

    // operations
    Iterator i = opSchemas.iterator();
    List ops = mach_.getOperations();
    while (i.hasNext())
      ops.add(operation((ConstDecl)i.next()));

    return mach_;
  }

  /** Converts an expanded Z schema into a BOperation */
  //@ requires schema != null;
  //@ requires schema.getExpr instanceof SchExpr;
  protected BOperation operation(ConstDecl schema) {
    String opName = schema.getDeclName().getWord();  // TODO: decorations?
    BOperation op = new BOperation(opName, mach_);
    Map inputs = varExtract_.getInputVariables(schema);
    Map outputs = varExtract_.getOutputVariables(schema);
    declareVars(inputs, op.getInputs(), op.getPre());
    declareVars(outputs, op.getOutputs(), op.getPost());
    // TODO: split the predicate parts into pre and post
    Pred post = ((SchExpr)schema.getExpr()).getSchText().getPred();
    addPred(post, op.getPost());
    return op;
  }

  /** Adds a set of names and type constraints to names/preds lists */
  protected void declareVars(Map vars, List names, List preds) {
    Iterator v = vars.keySet().iterator();
    while (v.hasNext()) {
      DeclName n = (DeclName)v.next();
      VarDecl decl = (VarDecl)vars.get(n);
      names.add(n);
      preds.add(Create.memPred(n, decl.getExpr()));
    }
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


  //==================== Visitor Methods for Paragraphs ==================

  /** This generic visit method recurses into all Z terms. */
  // TODO: make this throw an exception instead
  public Object visitTerm(Term term) {
    return VisitorUtils.visitTerm(this, term, true);
  }


  /** Adds all the given types to the 'parameters' list of a B machine. */
  public Object visitGivenPara(GivenPara p) {
    Map sets = mach_.getSets();
    Iterator v = p.getDeclName().iterator(); 
    while (v.hasNext()) {
      DeclName n = (DeclName)v.next();
      sets.put(n,null);
    }
    return p;
  }

  /** Adds a simple free type to a B machine */
  public Object visitFreetype(Freetype f) {
    Map sets = mach_.getSets();
    Iterator i = f.getBranch().iterator();

    // now we get all the branch names, and check they are simple.
    List/*<DeclName>*/ contents = new ArrayList();
    while (i.hasNext()) {
      Branch b = (Branch)i.next();
      if (b.getExpr() != null)
	throw new BException("free types must be simple enumerations");
      contents.add(b.getDeclName());
    }

    // Add  N == {b1,...,bn}  to the SETS part of the machine
    sets.put(f.getDeclName(), contents);
    return f;
  }

  /** Adds some axiomatic definitions to a B machine */
  public Object visitAxPara(AxPara p) {
    // TODO: ignore schema, but add all other defns and axioms
    return p;
  }

  /** Ignore conjecture paragraphs */
  public Object visitConjPara(ConjPara p) { return p; }

  /** Ignore narrative paragraphs */
  public Object visitNarrPara(NarrPara p) { return p; }

  /** Ignore operator template paragraphs */
  public Object visitOptempPara(OptempPara p) { return p; }

  /** Unparsed Z paragraphs cause the translaton to fail */
  public Object visitUnparsedPara(UnparsedPara p) {
    throw new RuntimeException("cannot translate an incomplete specification "
			 + "(unparsed paragraph)");
  }
}

