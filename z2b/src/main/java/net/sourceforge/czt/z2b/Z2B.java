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

import java.io.StringWriter;
import java.util.*;
import java.util.logging.Logger;

// the CZT classes for Z.
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.DefinitionType;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.z.util.CarrierSet;
import net.sourceforge.czt.util.CztException;
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
  implements TermVisitor<Object>,
             ListTermVisitor<Object>,
             LatexMarkupParaVisitor<Object>,
             GivenParaVisitor<Object>,
             FreeParaVisitor<Object>,
             FreetypeVisitor<Object>,
             AxParaVisitor<Object>,
             ConjParaVisitor<Object>,
             NarrParaVisitor<Object>,
             OptempParaVisitor<Object>,
             UnparsedParaVisitor<Object>,
             VarDeclVisitor<Object>,
             ConstDeclVisitor<Object>,
             ZDeclListVisitor<Object>,
             ZParaListVisitor<Object>,
             ZFreetypeListVisitor<Object>
{
  private BMachine mach_ = null;

  private FreeVarChecker freevarChecker_ = new FreeVarChecker();

  private SectionManager manager_;

  private Preprocessor preprocessor_ = new Preprocessor();

  public Z2B(SectionManager manager)
    throws UnfoldException
  {
    manager_ = manager;
  }

  private Factory getFactory()
  {
    return Create.getFactory();
  }

  /** Translates a ZSect into a BMachine.
   *  @param sect    the ZSect to be translated
   *
   *  <esc> requires varExtract != null </esc>
   */
  public BMachine makeBMachine(ZSect sect)
    throws BException, CommandException
  {
    SectTypeEnvAnn ann = (SectTypeEnvAnn)
      manager_.get(new Key(sect.getName(), SectTypeEnvAnn.class));
    Classifier classifier = new Classifier(ann);
    List<NameSectTypeTriple> stateSchemas = classifier.getState();
    List<NameSectTypeTriple> initSchemas = classifier.getInit();
    List<NameSectTypeTriple> opSchemas = classifier.getOps();

    // Check the state schema
    if (stateSchemas.size() != 1) {
      final StringBuilder msg = new StringBuilder();
      msg.append("Cannot find the state schema.");
      if (stateSchemas.size() > 1) {
        msg.append("  Possible candidates are: ");
        for (NameSectTypeTriple triple : stateSchemas) {
          msg.append(triple.getName().accept(new PrintVisitor()) + " ");
        }
      }
      throw new BException(msg.toString());
    }
    Expr stateSchemaDef = lookup(stateSchemas.get(0));
    if ( ! (stateSchemaDef instanceof SchExpr)) {
      throw new BException("state schema is not a simple schema");
    }
    NameSectTypeTriple state = stateSchemas.get(0);

    // Check the init schema
    if (initSchemas.size() != 1) {
      final StringBuilder msg = new StringBuilder();
      msg.append("Cannot find the initialization schema.");
      if (stateSchemas.size() > 1) {
        msg.append("  Possible candidates are: ");
        for (NameSectTypeTriple triple : stateSchemas) {
          msg.append(triple.getName().accept(new PrintVisitor()) + " ");
        }
      }
      throw new BException(msg.toString());
    }
    NameSectTypeTriple init = initSchemas.get(0);
    Expr initSchemaDef = lookup(init);
    if ( ! (initSchemaDef instanceof SchExpr)) {
      String msg = "init schema is not a simple schema: " + initSchemaDef;
      throw new BException(msg);
    }
    List<NameTypePair> ivars =
      getSignature(initSchemas.get(0)).getNameTypePair();

    // Check operation schemas
    if (opSchemas.size() == 0) {
      throw new BException("cannot find any operation schemas");
    }

    // TODO: extend this extractor to handle x==E vars.
    //       Idea: return a map from Name to Expr (type)
    Pred invar = ((SchExpr) stateSchemaDef).getZSchText().getPred();
    Pred initpred = ((SchExpr) initSchemaDef).getZSchText().getPred();

    mach_ = new BMachine(sect.getName());

    // Process all the non-schema definitions from sect
    sect.getParaList().accept(this);
    // Add state variables
    declareVars(state, mach_.getVariables(), mach_.getInvariant());
    // add any other invariant predicates
    if (invar != null) addPred(invar, mach_.getInvariant());

    // Add init conditions
    declareVars(init, new ArrayList<String>(), mach_.getInitialisation());
    if (initpred != null) addPred(initpred, mach_.getInitialisation());

    // operations
    List<BOperation> ops = mach_.getOperations();
    for (NameSectTypeTriple triple : opSchemas) {
      ops.add(operation(triple));
    }
    return mach_;
  }

  /**
   * Type is assumed to be of PowerType of SchemaType
   */
  protected Signature getSignature(NameSectTypeTriple triple)
  {
    PowerType powerType = (PowerType) triple.getType();
    SchemaType schemaType = (SchemaType) powerType.getType();
    return schemaType.getSignature();
  }

  protected Expr lookup(NameSectTypeTriple triple)
    throws CommandException
  {
    String sectName = triple.getSect();
    DefinitionTable defTable = (DefinitionTable)
      manager_.get(new Key(sectName, DefinitionTable.class));
    String name = triple.getName().accept(new PrintVisitor());

    //Expr result = defTable.lookup(name).getExpr();
    
    DefinitionTable.Definition def = defTable.lookup(name);
    // Added distinction with CONSTDECL, for compatibility with old DefinitionTable (Leo)      
    if (def == null || !def.getDefinitionType().equals(DefinitionType.CONSTDECL))
    {
      CztException ex =new CztException("Cannot find name: "+name);
      throw ex;
    }
    Expr result = def.getExpr();
    if (result == null)
    {
      CztException ex =new CztException("Cannot find name: "+name);
      throw ex;
    }
    System.out.print("Unfold ");
    print(result, sectName);
    result = (Expr) preprocessor_.unfold(result, sectName, manager_);
    System.out.print("to ");
    print(result, sectName);
    return result;
  }

  protected void print(Term term, String section)
  {
    StringWriter writer = new StringWriter();
    PrintUtils.print(term, writer, manager_, section, Markup.LATEX);
    System.out.println(writer.toString());
  }

  /**
   * Assumes that all the declarations are VarDecls
   */
  protected Map<ZName,Expr> getVariables(SchExpr schExpr, Class decor)
  {
    Map<ZName,Expr> result = new HashMap<ZName,Expr>();
    for (Decl decl : schExpr.getZSchText().getZDeclList()) {
      VarDecl varDecl;
      try {
        varDecl = (VarDecl) decl;
      }
      catch (ClassCastException ex) {
        throw new BException("Schema not unfolded");
      }
      for (Name name : varDecl.getZNameList()) {
        if (name instanceof ZName) {
          final ZName zName = (ZName) name;
          final ZStrokeList strokeList = zName.getZStrokeList();
          final int size = strokeList.size();
          if ((size == 0 && decor == null) ||
              (size > 0 && decor != null &&
               decor.isInstance(strokeList.get(strokeList.size() - 1)))) {
            result.put(zName, varDecl.getExpr());
          }
        }
      }
    }
    return result;
  }

  protected BOperation operation(NameSectTypeTriple triple)
    throws CommandException
  {
    final String opName = triple.getName().accept(new PrintVisitor());
    System.out.println("Processing " + opName);
    final BOperation op = new BOperation(opName, mach_);
    final ZSchText zSchText = ((SchExpr) lookup(triple)).getZSchText();
    for (Decl decl : zSchText.getZDeclList()) {
      final VarDecl varDecl = (VarDecl) decl;
      final Expr expr = varDecl.getExpr();
      for (Name name : varDecl.getZNameList()) {
        ZName zName = (ZName) name;
        ZStrokeList strokes = zName.getZStrokeList();
        if (strokes.size() > 0) {
          Stroke last = strokes.get(strokes.size() - 1);
          if (last instanceof InStroke) {
            declareVar(zName, expr, op.getInputs(), op.getPre());
          }
          else if (last instanceof OutStroke) {
            declareVar(zName, expr, op.getOutputs(), op.getPost());
          }
          else if (last instanceof NextStroke) {
            declareVar(zName, expr, new ArrayList<String>(), op.getPost());
          }
        }
      }
    }
    // TODO: split the predicate parts into pre and post
    Pred post = zSchText.getPred();
    List<Pred> prePreds = new ArrayList<Pred>();
    List<Pred> postPreds = new ArrayList<Pred>();
    splitPrePost(post, prePreds, postPreds);
    addPreds(prePreds, op.getPre());
    addPreds(postPreds, op.getPost());
    return op;
  }

  /**
   * Adds the string representionat of <code>zName</code> to the names
   * list and a membership of <code>zName</code> in the given
   * expression to the preds list.
   */
  protected void declareVar(ZName zName, Expr expr,
                            List<String> names,
                            List<Pred> preds)
  {
    names.add(zName.accept(new PrintVisitor()));
    preds.add(getFactory().createMemPred(zName, expr));
  }

  /** Adds ALL the names in a VarDecl to the names/preds lists. */
  protected void declareVars(VarDecl decl,
                             List<String> names,
                             List<Pred> preds)
  {
    for (Name name : decl.getZNameList()) {
      declareVar((ZName) name, decl.getExpr(), names, preds);
    }
  }

  protected void declareVars(List<NameTypePair> vars,
                             List<String> names,
                             List<Pred> preds)
  {
    CarrierSet carrier = new CarrierSet();
    for (NameTypePair pair : vars) {
      Expr expr = (Expr) pair.getType().accept(carrier);
      declareVar(pair.getZName(), expr, names, preds);
    }
  }

  protected void declareVars(NameSectTypeTriple triple,
                             List<String> names,
                             List<Pred> preds)
    throws CommandException
  {
    SchExpr schema = (SchExpr) lookup(triple);
    for (Decl decl : schema.getZSchText().getZDeclList()) {
      VarDecl varDecl = (VarDecl) decl;
      declareVars((VarDecl) decl, names, preds);
    }
  }

  /** Flatten conjuncts and add them to the given list. */
  //@ requires pred != null;
  protected void addPred(Pred pred, List<Pred> preds)
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
  protected void addPreds(List<Pred> inpreds, List<Pred> preds)
  {
    for (Pred p : inpreds) {
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
  protected void splitPrePost(Pred pred, List<Pred> pre, List<Pred> post)
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
    Map<String,List<String>> sets = mach_.getSets();
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
    Map<String,List<String>> sets = mach_.getSets();
    Iterator<Branch> i = assertZBranchList(freetype.getBranchList()).iterator();
    // now we get all the branch names, and check they are simple.
    List<String> contents = new ArrayList<String>();
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
    for (Decl decl : zDeclList) decl.accept(this);
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
