package net.sourceforge.czt.z2alloy.visitors;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.z.ast.Exists1Pred;
import net.sourceforge.czt.z.ast.ExistsExpr;
import net.sourceforge.czt.z.ast.ForallPred;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.visitor.ExistsExprVisitor;
import net.sourceforge.czt.z2alloy.Z2Alloy;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.Enum;
import net.sourceforge.czt.z2alloy.ast.ExprBinary;
import net.sourceforge.czt.z2alloy.ast.ExprCall;
import net.sourceforge.czt.z2alloy.ast.ExprConstant;
import net.sourceforge.czt.z2alloy.ast.ExprITE;
import net.sourceforge.czt.z2alloy.ast.ExprLet;
import net.sourceforge.czt.z2alloy.ast.ExprQuant;
import net.sourceforge.czt.z2alloy.ast.ExprUnary;
import net.sourceforge.czt.z2alloy.ast.ExprVar;
import net.sourceforge.czt.z2alloy.ast.Field;
import net.sourceforge.czt.z2alloy.ast.Func;
import net.sourceforge.czt.z2alloy.ast.PrimSig;
import net.sourceforge.czt.z2alloy.ast.Sig;
import net.sourceforge.czt.z2alloy.ast.VisitReturn;

public class ExistsExprVisitorImpl extends AbstractVisitor implements
ExistsExprVisitor<AlloyExpr>
{

  private final String name_;

  public ExistsExprVisitorImpl(String name) {
    name_ = name; 
  }

  /*
   * gives the list of variables quantified over and the predicate
   * the predicate comes from if a schema is included in the decls
   */
  public Pair<List<ExprVar>, AlloyExpr> processQuantPredDecls(QntPred qntPred) {
    // these should come in two varieties
    // some are just ExprVar, which are nice
    // others are sigs, which are more complex
    List<AlloyExpr> decls = new ZDeclListVisitorImpl().visitZDeclList(qntPred.getZSchText().getZDeclList());

    List<String> inclDeclOrder = new ArrayList<String>();
    Map<String, AlloyExpr> inclDecls = new HashMap<String, AlloyExpr>();

    AlloyExpr sigPred = null;

    for (AlloyExpr alloyExpr : decls) {
      // just make a new expr var for the list
      if (alloyExpr instanceof ExprVar) {
        ExprVar exprVar = (ExprVar) alloyExpr;
        inclDeclOrder.add(exprVar.label());
        inclDecls.put(exprVar.label(), exprVar.expr());
      }
      else if (alloyExpr instanceof Sig) {
        Sig inclSig = (Sig) alloyExpr;
        // include all the fields in the list
        for (Field f : inclSig) {
          inclDeclOrder.add(f.label());
          inclDecls.put(f.label(), f.expr());
        }
        Func func = Z2Alloy.getInstance().module().getFunc("pred_" + inclSig.label());
        // if there is a sig pred, call it and include it as a pred
        if (func != null) {
          AlloyExpr temp = func.call(inclSig.fields());
          if (sigPred == null) {
            sigPred = temp;
          }
          else {
            sigPred = sigPred.and(temp);
          }
        }
      }
      // not sure what other types there could be
      else {
        System.err.println("not yet implemented");
        throw new RuntimeException();
      }
    }

    if (inclDeclOrder.isEmpty()) {
      System.err.println("quantifier predicates must include declared variables");
      throw new RuntimeException();
    }

    List<ExprVar> rest = new ArrayList<ExprVar>();
    for (String label : inclDeclOrder) {
      rest.add(new ExprVar(label, inclDecls.get(label)));
    }
    return new Pair<List<ExprVar>, AlloyExpr>(rest, sigPred);
  }

  /**
   * gives the predicate for a quantification pred
   * differs slightly for existential and universal quantifiers
   */
  public AlloyExpr processQuantPred(QntPred qntPred, boolean exists, AlloyExpr declPred) {
    Pair<List<ExprVar>, AlloyExpr> decls = processQuantPredDecls(qntPred);

    AlloyExpr pred;
    Z2Alloy.getInstance().body = true;

    AlloyExpr pred1 = visit(qntPred.getZSchText().getPred());
    AlloyExpr pred2 = visit(qntPred.getPred());

    Z2Alloy.getInstance().body = false;

    if (pred2 == null) {
      System.err.println("pred of qntPred must not be null");
      throw new RuntimeException();
    }
    if (decls.getSecond() != null) {
      if( pred1 == null) {
        pred1 = decls.getSecond();
      }
      else {
        pred1 = pred1.and(decls.getSecond());
      }
    }
    if (pred1 == null) {
      pred = pred2;
    } else {
      if (exists) {
        pred = pred1.and(pred2);
      }
      else {
        pred = pred1.implies(pred2);
      }
    }
    
    if (decls.getFirst().isEmpty()) {
      System.err.println("quantifier predicates must include declared variables");
      throw new RuntimeException();
    }
    return pred;
  }

  /**
   * uses visit to recurisvely translate variables and predicates
   * 
   * <pre>
   * \forall var1, ..., varn @ pred1 | pred2
   * </pre>
   * 
   * translates to:
   * 
   * <pre>
   * all var1, ..., var2 | pred1 =&gt; pred2
   * </pre>
   */
  public AlloyExpr visitForallPred(ForallPred allPred) {
    Pair<List<ExprVar>, AlloyExpr> decls = processQuantPredDecls(allPred);
    AlloyExpr pred = processQuantPred(allPred, false, decls.getSecond());
    return pred.forAll((decls.getFirst()));
  }

  /**
   * uses visit to recursively translate variables and predicates.
   * 
   * <pre>
   * \exists_1 var1, ... varn @ pred1 | pred2
   * </pre>
   * 
   * translates to :
   * 
   * <pre>
   * one var1, ..., varn | pred1 and pred2
   * </pre>
   * 
   * @return the expression, or null if something is null that should not be
   */
  public AlloyExpr visitExists1Pred(Exists1Pred exists1Pred) {
    Pair<List<ExprVar>, AlloyExpr> decls = processQuantPredDecls(exists1Pred);
    AlloyExpr pred = processQuantPred(exists1Pred, true, decls.getSecond());
    return pred.forOne(decls.getFirst());
  }

  /*
   * 
   */
  public Pair<Map<String, AlloyExpr>, List<ExprVar>> includedVariables(List<AlloyExpr> incl) {
    Map<String, AlloyExpr> replaceVars = new HashMap<String, AlloyExpr>();
    List<ExprVar> decls = new ArrayList<ExprVar>();

    for (AlloyExpr alloyExpr : incl) {
      if (alloyExpr instanceof Sig) {
        Sig inclSig = (Sig) alloyExpr;
        ExprVar sigVar = new ExprVar(inclSig.label() + "_temp", inclSig);
        decls.add(sigVar);
        for (Field f : inclSig.fields()) {
          replaceVars.put(f.label(), sigVar.join(new ExprVar(f.label(), f.expr())));
        }
      }
      else if (alloyExpr instanceof ExprVar) {
        ExprVar inclExprVar = (ExprVar) alloyExpr;
        replaceVars.put(inclExprVar.label(), new ExprVar(inclExprVar.label(), inclExprVar.expr()));
        decls.add(inclExprVar);
      }
      else {
        System.err.println("not yet translated");
        throw new RuntimeException();
      }
    }  
    return new Pair<Map<String, AlloyExpr>, List<ExprVar>>(replaceVars, decls);
  }
  
  public Map<String, List<AlloyExpr>> dups(List<AlloyExpr> incl) {
    Map<String, List<AlloyExpr>> dups = new HashMap<String, List<AlloyExpr>>();
    for (AlloyExpr alloyExpr : incl) {
      if (alloyExpr instanceof Sig) {
        Sig inclSig = (Sig) alloyExpr;
        ExprVar sigVar = new ExprVar(inclSig.label() + "_temp", inclSig);
        for (Field f : inclSig) {
          if (!dups.containsKey(f.label())) {
            dups.put(f.label(), new ArrayList<AlloyExpr>());
          }
          dups.get(f.label()).add(sigVar.join(new ExprVar(f.label(), f.expr())));
        }
      }
      else if (alloyExpr instanceof ExprVar) {
        ExprVar inclExprVar = (ExprVar) alloyExpr;
        if (!dups.containsKey(inclExprVar.label())) {
          dups.put(inclExprVar.label(), new ArrayList<AlloyExpr>());
        }
        dups.get(inclExprVar.label()).add(inclExprVar);
      }
    }
    
    return dups;
  }

  /**
   * Creates a new signiture which contains all the fields in the predicate
   * schemas, except those in schemas quantified over <br>
   * Includes a signiture predicate which is an exists predicate translated
   * from the schema predicate, with the additon that any fields in more than
   * one predicate schema are equal <br>
   * eg
   * 
   * <pre>
   * A == \exists B, C @ D \and E
   * </pre>
   * 
   * <br>
   * where B has fields b:X, C has fields b:X, c:Y, D has fields b : X, c : Y,
   * d : Z, E has field b : X translates to:
   * 
   * <pre>
   * sig A {
   *    d : Z
   * }{pred_A[d]}
   * pred pred_A[d : Z] {
   *    some b_temp : B, c_temp : C | pred_D[c_temp.b, c_temp.c, d] and pred_E[c_temp.b] and c_temp.b = b_temp.b
   * }
   * 
   */

  /*
   * the idea of this is to get five different pieces of information:
   * i) a set of all the included in the predicate part
   * ii) all the declared variables
   * iii) a map of where the fields needed by the sigs come from
   * iv) the fields needed by the sigs in the predicate but which aren't quantified over
   * v) the predicate part, including the correct expression for all the variables (from ii)
   * 
   * 
   */
  public AlloyExpr visitExistsExpr(ExistsExpr existsExpr) {
    List<AlloyExpr> incl = new ZDeclListVisitorImpl().visitZDeclList(existsExpr.getZSchText().getZDeclList());
    
    // gets the declared variables, and maps the names to the expression for the variables used in the predicate
    Pair<Map<String, AlloyExpr>, List<ExprVar>> includedVariables = includedVariables(incl);

    Map<String, AlloyExpr> variables = includedVariables.getFirst();

    // gets the predicate part
    AlloyExpr zPred = visit(existsExpr.getExpr());
    AlloyExpr zDeclPred = visit(existsExpr.getZSchText().getPred());
    
    // gets the sigs used in the predicate
    Set<Sig> inclSigs = new SigVisitor().visitThis(zPred);

    // gets all the fields from all the sigs collected above
    // removed duplicates
    List<Field> totalFields = fields(inclSigs);    

    // the fields that still need to be included in the final signature
    // also includes them in the mapping for use in the predicate
    List<Field> remainingFields = new ArrayList<Field>();
    for (Field f : totalFields) {
      if (! variables.containsKey(f.label())) {
        variables.put(f.label(), new ExprVar(f.label(), f.expr()));
        remainingFields.add(f);
      }
    }
    // builds up the new signature
    Sig sig = new PrimSig(name_);
    for (Field f : totalFields) {
      sig.addField(f);
    }
    Z2Alloy.getInstance().addSig(sig);
    // uses the predicate, but replaces the variables so they come from the right place
    AlloyExpr pred = new ReplaceVariables(variables).visitThis(zPred);

    AlloyExpr dupPred = fixDups(dups(incl));
    
    pred = (dupPred == null ? pred : pred.and(dupPred));

    if (zDeclPred != null) {
      AlloyExpr declPred = new ReplaceVariables(variables).visitThis(zDeclPred);
      pred = pred.and(declPred);
    }
    
    Z2Alloy.getInstance().addSigPred(sig, pred.forSome(includedVariables.getSecond()));
    return null;
  }
  
  private AlloyExpr fixDups(Map<String, List<AlloyExpr>> dupMap) {
    AlloyExpr pred = null;
    
    for (Entry<String, List<AlloyExpr>> entry : dupMap.entrySet()) {
      List<AlloyExpr> dups = entry.getValue();
      if (dups.size() > 1) {
        AlloyExpr temp = null;
        AlloyExpr first = dups.get(0);
        for (int i = 1; i < dups.size(); i++) {
          if (temp == null) {
            temp = dups.get(i).equal(first);
          }
          else {
            temp = temp.and(dups.get(i).equal(first));
          }
        }
        pred = (pred == null ? temp : pred.and(temp));
      }
    }
    
    return pred;
  }

  // just collects up the fields
  // calls stripFields to remove dups
  private List<Field> fields(Set<Sig> sigs) {
    List<Field> fields = new ArrayList<Field>();
    for (Sig s : sigs) {
      for (Field f : s.fields()) {
        fields.add(f);
      }
    }
    return stripFields(fields);
  }

  /*
   * this just collects up included signatures
   * the idea is that both sides of exprbinaries are included, exprcalls
   * are translated back into the sig they represent
   * 
   *  unexpected parts of the ast cause a RuntimeException
   */
  private class SigVisitor extends VisitReturn<Set<Sig>> {

    public Set<Sig> visit(ExprBinary x) {
      Set<Sig> ret = new HashSet<Sig>();
      ret.addAll(this.visitThis(x.left()));
      ret.addAll(this.visitThis(x.right()));
      return ret;
    }

    public Set<Sig> visit(ExprCall x) {
      Set<Sig> ret = new HashSet<Sig>();
      ret.add(Z2Alloy.getInstance().module().getSig(x.fun().label().replaceFirst("pred_", "")));
      return ret;
    }

    public Set<Sig> visit(Sig x) {
      Set<Sig> ret = new HashSet<Sig>();
      ret.add(x);
      return ret;
    }


    public Set<Sig> visit(ExprConstant x) { throw new RuntimeException(); }
    public Set<Sig> visit(ExprITE x) { throw new RuntimeException(); }
    public Set<Sig> visit(ExprLet x) { throw new RuntimeException(); }
    public Set<Sig> visit(ExprQuant x) { throw new RuntimeException(); }
    public Set<Sig> visit(ExprUnary x) { throw new RuntimeException(); }
    public Set<Sig> visit(ExprVar x) { throw new RuntimeException(); }
    public Set<Sig> visit(Field x) { throw new RuntimeException(); }
    public Set<Sig> visit(Enum x) { throw new RuntimeException(); }

  }

  /*
   * replaces variables with the given ones
   * also turns signatures into calls for the correct predicate
   *
   */
  private class ReplaceVariables extends VisitReturn<AlloyExpr> {
    private Map<String, AlloyExpr> replaceVariables_;

    private ReplaceVariables(Map<String, AlloyExpr> replaceVariables) {
      replaceVariables_ = replaceVariables;
    }

    public AlloyExpr visit(ExprBinary x) {
      return new ExprBinary(x.op(), visitThis(x.left()), visitThis(x.right()));
    }

    public AlloyExpr visit(ExprCall x) {
      Func f = x.fun();
      List<AlloyExpr> args = new ArrayList<AlloyExpr>();
      for (ExprVar exprVar : f.params()) {
        args.add(replaceVariables_.get(exprVar.label()));
      }
      return f.call(args);
    }

    public AlloyExpr visit(Sig x) {
      Func f = Z2Alloy.getInstance().module().getFunc("pred_" + x.label());
      if (f == null) {
        return ExprConstant.TRUE;
      }
      List<AlloyExpr> args = new ArrayList<AlloyExpr>();
      for (ExprVar exprVar : f.params()) {
        args.add(replaceVariables_.get(exprVar.label()));
      }
      return f.call(args);
    }

    public AlloyExpr visit(ExprConstant x) {
      return x;
    }
    
    public AlloyExpr visit(ExprITE x) {
      return new ExprITE(
          visitThis(x.cond()),
          visitThis(x.left()),
          visitThis(x.right())
      );
    }
    
    public AlloyExpr visit(ExprLet x) {
      Map<String, AlloyExpr> updates = new HashMap<String, AlloyExpr>(replaceVariables_);
      updates.put(x.label().label(), x.label());
      
      return new ExprLet(
          x.label(),
          visitThis(x.var()),
          new ReplaceVariables(updates).visitThis(x.sub())
      );
    }
    
    public AlloyExpr visit(ExprQuant x) {
      List<ExprVar> newVars = new ArrayList<ExprVar>();
      Map<String, AlloyExpr> updates = new HashMap<String, AlloyExpr>(replaceVariables_);
      
      for (ExprVar exprVar : x.vars()) {
        newVars.add(new ExprVar(exprVar.label(), visitThis(exprVar.expr())));
        updates.put(exprVar.label(), exprVar);
      }
      
      return new ExprQuant(
          x.op(),
          newVars,
          new ReplaceVariables(updates).visitThis(x.sub())
      );
      
    }
    public AlloyExpr visit(ExprUnary x) {
      return new ExprUnary(x.op(), visitThis(x.sub()));
    }
    public AlloyExpr visit(ExprVar x) {
      if (replaceVariables_.containsKey(x.label())) {
        return replaceVariables_.get(x.label());
      }
      return new ExprVar(x.label(), visitThis(x.expr()));
    }
    public AlloyExpr visit(Field x) {
      return x;
    }
    public AlloyExpr visit(Enum x) {
      return x;
    }

  }

  // just removes duplicate fields
  // doesn't try to do anythin tricky with types, just uses the first one
  // TODO Clare make this work properly wrt types
  private List<Field> stripFields(List<Field> list) {
    Set<String> incl = new HashSet<String>();
    List<Field> ret = new ArrayList<Field>();
    for (Field field : list) {
      if (incl.add(field.label())) {
        ret.add(field);
      }
    }
    return ret;
  }
}
