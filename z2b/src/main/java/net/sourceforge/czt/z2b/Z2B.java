/**
Copyright (C) 2003, 2004, 2006 Mark Utting
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
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.visitor.*;
import static net.sourceforge.czt.z.util.ZUtils.*;

/**
 * <p>This class converts a Z section into a B machine.
 *
 * @author Mark Utting
 */
public class Z2B
  implements TermVisitor,
             ListTermVisitor,
             LatexMarkupParaVisitor,
             GivenParaVisitor,
             FreeParaVisitor,
             FreetypeVisitor,
             AxParaVisitor,
             ConjParaVisitor,
             NarrParaVisitor,
             OptempParaVisitor,
             UnparsedParaVisitor,
             VarDeclVisitor,
             ConstDeclVisitor,
             ZParaListVisitor,
             ZFreetypeListVisitor
{
  private static final Logger sLogger
    = Logger.getLogger("net.sourceforge.czt.z2b");

  /* That needs to be reimplemented
  // plugins for finding/classifying schemas and variables.
  private SchemaExtractor extractor_;
  private SchemaIdentifier identify_;
  private VariableExtractor varExtract_;
  */

  private BMachine mach_ = null;

  private FreeVarChecker freevarChecker_ = new FreeVarChecker();

  /**
  * Constructor for Z2B converter.
  *
  * @param plugins Plugins to analyze the specification.
  public Z2B(PluginList plugins)
    throws PluginInstantiationException
  {
    VisitorUtils.checkVisitorRules(this);
    extractor_ = (SchemaExtractor) plugins.getPlugin(SchemaExtractor.class);
    identify_ = (SchemaIdentifier) plugins.getPlugin(SchemaIdentifier.class);
    varExtract_ =
      (VariableExtractor) plugins.getPlugin(VariableExtractor.class);
  }
  */

  private Factory getFactory()
  {
    return Create.getFactory();
  }

  /** Translates a ZSect into a BMachine.
   *  @param spec  the complete spec, which contains the ZSect
   *  @param sect  the ZSect to be translated
   *  @param url   the source location of the Z specification.
   *
   *  <esc> requires varExtract != null </esc>
   */
  public BMachine makeBMachine(Spec spec, ZSect sect, URL url)
    throws BException
  {
    List/*<ConstDecl<SchExpr>>*/ schemas;
    ConstDecl/*<SchExpr>*/ stateSchema;
    ConstDecl/*<SchExpr>*/ initSchema;
    List/*<ConstDecl<SchExpr>>*/ opSchemas;

    /*
    // find all the schemas
    schemas = extractor_.getSchemas(spec);

    // classify the schemas into state/init/operation.
    identify_.identifySchemas(spec, schemas);
    stateSchema = identify_.getStateSchema();
    initSchema = identify_.getInitSchema();
    opSchemas = identify_.getOperationSchemas();

    // Now check that the plugins have found a valid state schema
    if (stateSchema == null)
        throw new BException("cannot find the state schema");
    if ( ! (stateSchema.getExpr() instanceof SchExpr))
        throw new BException("state schema is not a simple schema");
    Map svars = varExtract_.getStateVariables(stateSchema);
    if (svars == null || svars.size() == 0)
        throw new BException("state schema contains no variables!");
    if (varExtract_.getPrimedVariables(stateSchema).size() != 0
	|| varExtract_.getNumberedVariables(stateSchema).size() != 0
        || varExtract_.getInputVariables(stateSchema).size() != 0
        || varExtract_.getOutputVariables(stateSchema).size() != 0)
        throw new BException("state schema contains decorated variables");

    // Check the init schema
    if (initSchema == null)
        throw new BException("cannot find the initialization schema");
    if ( ! (initSchema.getExpr() instanceof SchExpr))
        throw new BException("init schema is not a simple schema: "
			     +initSchema.getExpr());
    Map initvars = varExtract_.getStateVariables(initSchema);
    if (initvars == null || initvars.size() == 0)
      throw new BException("cannot find any unprimed vars in init schema");
    if (varExtract_.getPrimedVariables(initSchema).size() != 0
      || varExtract_.getNumberedVariables(initSchema).size() != 0
      || varExtract_.getInputVariables(initSchema).size() != 0
      || varExtract_.getOutputVariables(initSchema).size() != 0) {
      throw new BException("init schema contains decorated variables");
    }

    if (initvars.size() != svars.size())
      throw new BException("init has "+initvars.size()
			   +" variables, but state has "+svars.size());
    if (opSchemas == null || opSchemas.size() == 0)
      throw new BException("cannot find any operation schemas");

    // TODO: extend this extractor to handle x==E vars.
    //       Idea: return a map from Name to Expr (type)
    Pred invar = ((SchExpr) stateSchema.getExpr()).getZSchText().getPred();
    Pred initpred = ((SchExpr) initSchema.getExpr()).getZSchText().getPred();

    mach_ = new BMachine(sect.getName(), url.toString());

    // Process all the non-schema definitions from sect
    sect.getParaList().accept(this);

    // Add state variables
    declareVars(svars, mach_.getVariables(), mach_.getInvariant());
    // add any other invariant predicates
    if (invar != null)
      addPred(invar, mach_.getInvariant());

    // Add init conditions
    declareVars(initvars, new ArrayList(), mach_.getInitialisation());
    if (initpred != null)
      addPred(initpred, mach_.getInitialisation());

    // operations
    Iterator i = opSchemas.iterator();
    List ops = mach_.getOperations();
    while (i.hasNext())
      ops.add(operation((ConstDecl) i.next()));

    return mach_;
    */
    return null;
  }

  /** Converts an expanded Z schema into a BOperation. */
  //@ requires schema != null;
  //@ requires schema.getExpr instanceof SchExpr;
  protected BOperation operation(ConstDecl schema)
  {
    String opName = schema.getZName().getWord();  // TODO: decorations?
    BOperation op = new BOperation(opName, mach_);
    /*
    Map inputs = varExtract_.getInputVariables(schema);
    Map outputs = varExtract_.getOutputVariables(schema);
    declareVars(inputs, op.getInputs(), op.getPre());
    declareVars(outputs, op.getOutputs(), op.getPost());
    // Now add the type conditions of the prime vars to post
    Map primed = varExtract_.getPrimedVariables(schema);
    declareVars(primed, new ArrayList(), op.getPost());
    // TODO: split the predicate parts into pre and post
    Pred post = ((SchExpr) schema.getExpr()).getZSchText().getPred();
    List prePreds = new ArrayList();
    List postPreds = new ArrayList();
    splitPrePost(post, prePreds, postPreds);
    addPreds(prePreds, op.getPre());
    addPreds(postPreds, op.getPost());
    */
    return op;
  }

  /** Adds ALL the names in a VarDecl to the names/preds lists. */
  protected void declareVars(VarDecl decl, List names, List preds)
  {
    Iterator i = decl.getName().iterator();
    while (i.hasNext()) {
      ZName declName = (ZName) i.next();
      names.add(declName.accept(new PrintVisitor()));
      ZName refName = getFactory().createZName(declName);
      preds.add(getFactory().createMemPred(refName, decl.getExpr()));
    }
  }

  /** Adds a set of names and type constraints to names/preds lists.
  *   This is intended to be used on the Map (from Name to VarDecl) objects
  *   returned from the gaffe-generator plugins.
  */
  protected void declareVars(Map vars, List names, List preds)
  {
    Iterator i = vars.keySet().iterator();
    while (i.hasNext()) {
      ZName declName = (ZName) i.next();
      VarDecl decl = (VarDecl) vars.get(declName);
      names.add(declName.accept(new PrintVisitor()));
      ZName refName = getFactory().createZName(declName);
      preds.add(getFactory().createMemPred(refName, decl.getExpr()));
    }
  }

  /** Flatten conjuncts and add them to the given list. */
  //@ requires pred != null;
  protected void addPred(Pred pred, List preds)
  {
    assert(pred != null);
    if (pred instanceof AndPred) {
      AndPred and = (AndPred) pred;
      addPred(and.getLeftPred(), preds);
      addPred(and.getRightPred(), preds);
    }
    else {
      preds.add(pred);
    }
  }

  /** Apply addPred to a LIST of predicates. */
  protected void addPreds(List inpreds, List preds)
  {
    Iterator i = inpreds.iterator();
    while (i.hasNext()) {
      Pred p = (Pred) i.next();
      addPred(p, preds);
    }
  }

  /** Split a complex postcondition predicate into pre/post lists.
      This currently uses a very simplistic algorithm.
      It splits post into conjuncts and puts all conjuncts that
      do not involve primed or output variables into 'pre', and
      all remaining conjuncts into 'post'.  This is not always
      correct, since some conjuncts that involve primes/outputs
      may add implicit constraints on inputs.

      TODO: improve the algorithm further.
   */
  protected void splitPrePost(Pred pred, List pre, List post)
  {
    if (pred instanceof AndPred) {
      AndPred and = (AndPred) pred;
      splitPrePost(and.getLeftPred(), pre, post);
      splitPrePost(and.getRightPred(), pre, post);
    }
    else {
      if (freevarChecker_.containsPrimesOrOutputs(pred))
        post.add(pred);
      else
        pre.add(pred);
    }
  }

  //==================== Visitor Methods for Paragraphs ==================

  /** This generic visit method is called whenever no other
  *   visit method matches the current term.
  *   Since we want to explicitly handle each kind of top-level
  *   term, we throw an exception to report unexpected kinds of terms.
  */
  public Object visitTerm(Term term)
  {
    throw new BException("unknown Z term: " + term);
  }

  /**
   * Visits a list term by visiting all its children.
   */
  public Object visitListTerm(ListTerm term)
  {
    VisitorUtils.visitTerm(this, term);
    return null;
  }

  public Object visitZParaList(ZParaList list)
  {
    VisitorUtils.visitTerm(this, list);
    return null;
  }

  /** Adds all the given types to the 'parameters' list of a B machine. */
  public Object visitGivenPara(GivenPara para)
  {
    Map sets = mach_.getSets();
    for (Name name : para.getNames()) {
      sets.put(name.accept(new PrintVisitor()), null);
    }
    return null;
  }


  /** Process all free types. */
  public Object visitFreePara(FreePara para)
  {
    para.getFreetypeList().accept(this);
    return null;
  }

  public Object visitZFreetypeList(ZFreetypeList list)
  {
    for (Freetype freetype : list)
    {
      freetype.accept(this);
    }
    return null;
  }

  /** Ignore Latex markup paragraphs. */
  public Object visitLatexMarkupPara(LatexMarkupPara para)
  {
    return null;
  }

  /** Adds a simple free type to a B machine. */
  public Object visitFreetype(Freetype freetype)
  {
    Map sets = mach_.getSets();
    Iterator i = assertZBranchList(freetype.getBranchList()).iterator();
    // now we get all the branch names, and check they are simple.
    List/*<String>*/ contents = new ArrayList();
    while (i.hasNext()) {
      Branch branch = (Branch) i.next();
      if (branch.getExpr() != null)
        throw new BException("free types must be simple enumerations, but "
			     +branch.getName()+" branch has expression "
			     +branch.getExpr());
      contents.add(branch.getName().accept(new PrintVisitor()));
    }
    // Add  N == {b1,...,bn}  to the SETS part of the machine
    sets.put(freetype.getName().accept(new PrintVisitor()), contents);
    return null;
  }

  /** Adds some axiomatic definitions to a B machine. */
  public Object visitAxPara(AxPara para)
  {
    if (para.getName().size() > 0)
      throw new BException("Generic definitions not handled yet.");
    ZSchText schText = para.getZSchText();
    schText.getDeclList().accept(this);
    Pred pred = schText.getPred();
    if (pred != null)
      addPred(pred, mach_.getProperties());
    return null;
  }

  public Object visitZDeclList(ZDeclList zDeclList)
  {
    zDeclList.getDecl().accept(this);
    return null;
  }

  /** Ignore conjecture paragraphs. */
  public Object visitConjPara(ConjPara para)
  {
    return null;
  }

  /** Ignore narrative paragraphs. */
  public Object visitNarrPara(NarrPara para)
  {
    return null;
  }

  /** Ignore operator template paragraphs. */
  public Object visitOptempPara(OptempPara para)
  {
    return null;
  }

  /** Unparsed Z paragraphs cause the translaton to fail. */
  public Object visitUnparsedPara(UnparsedPara para)
  {
    throw new BException("cannot translate an incomplete specification "
                         + "(unparsed paragraph)");
  }

  //=============== visit methods for Decls inside AxPara ============
  public Object visitVarDecl(VarDecl decl)
  {
    declareVars(decl, mach_.getConstants(), mach_.getProperties());
    return null;
  }

  public Object visitConstDecl(ConstDecl decl)
  {
    if ( ! (decl.getExpr() instanceof SchExpr)) {
      String name = decl.getName().accept(new PrintVisitor());
      mach_.getDefns().put(name, decl.getExpr());
    }
    return null;
  }
}
