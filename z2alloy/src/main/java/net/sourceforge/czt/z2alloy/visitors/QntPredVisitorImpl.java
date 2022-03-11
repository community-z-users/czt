package net.sourceforge.czt.z2alloy.visitors;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Exists1Pred;
import net.sourceforge.czt.z.ast.ExistsPred;
import net.sourceforge.czt.z.ast.ForallPred;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.visitor.Exists1PredVisitor;
import net.sourceforge.czt.z.visitor.ExistsPredVisitor;
import net.sourceforge.czt.z.visitor.ForallPredVisitor;
import net.sourceforge.czt.z.visitor.QntPredVisitor;
import net.sourceforge.czt.z2alloy.Z2Alloy;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.ExprVar;
import net.sourceforge.czt.z2alloy.ast.Field;
import net.sourceforge.czt.z2alloy.ast.Func;
import net.sourceforge.czt.z2alloy.ast.Sig;

public class QntPredVisitorImpl extends AbstractVisitor implements
  QntPredVisitor<AlloyExpr>,
  ForallPredVisitor<AlloyExpr>,
  ExistsPredVisitor<AlloyExpr>,
  Exists1PredVisitor<AlloyExpr>
{

public AlloyExpr visitQntPred(QntPred qntPred) {
  if (qntPred != null) {
    return qntPred.accept(this);
  }
  return null;
}

/*
 * gives the list of variables quantified over and the predicate
 * the predicate comes from if a schema is included in the decls
 */
public Pair<List<ExprVar>, AlloyExpr> processQuantPredDecls(QntPred qntPred) {
  // these should come in two varieties
  // some are just ExprVar, which are nice
  // others are sigs, which are more complex
  List<AlloyExpr> decls = visitZDeclList(qntPred.getZSchText().getZDeclList());

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
 * uses visit to recursively translate variables and predicates.
 * 
 * <pre>
 * \exists var1, ..., varn @ pred1 | pred2
 * </pre>
 * 
 * translates to
 * 
 * <pre>
 * some var1, ... var2 | pred1 and pred2
 * </pre>
 * 
 * @return the epxression, or null if something is null that should not be
 */
public AlloyExpr visitExistsPred(ExistsPred existsPred) {
  Pair<List<ExprVar>, AlloyExpr> decls = processQuantPredDecls(existsPred);
  AlloyExpr pred = processQuantPred(existsPred, true, decls.getSecond());
  return pred.forSome(decls.getFirst());
}

/**
 * uses visit to recursively translate the elements fo the ZDeclList <br/>
 * sets internally a list containing translations all elements other than
 * the first, in order
 * 
 * @return the first element
 */
public List<AlloyExpr> visitZDeclList(ZDeclList zDeclList) {
  Iterator<Decl> iter = zDeclList.iterator();
  List<AlloyExpr> ret = new ArrayList<AlloyExpr>();
  while (iter.hasNext()) {
    ret.add(visit(iter.next()));
  }
  return ret;
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

}