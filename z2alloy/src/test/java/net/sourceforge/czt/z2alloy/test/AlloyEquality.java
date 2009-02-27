package net.sourceforge.czt.z2alloy.test;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.Map.Entry;

import net.sourceforge.czt.z2alloy.Z2Alloy;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQuant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Func;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.parser.Module;

public class AlloyEquality
{
  
/**
 * checks that a Z2Alloy module and an Alloy Module are equal: the signitures are equal, the facts are equal, the funcs are equal
 * <br>
 * essentially checks that the names and types of sigs, facts, and funcs are the same.
 * 
 * @return true if all sigs, facts, and funcs are equal, false otherwise
 */  
  public static boolean equals(Z2Alloy z2alloy, Module module)
  {
    return equalsSigs(z2alloy, module) && equalsFacts(z2alloy, module) && equalsFuncs(z2alloy, module);
  }
  /**
   * Matches up the sigs from each module by their label. Recursively calls equalsSig on each pair. Removes this/ from the start of sigs in the Module
   * 
   * @return true is all sigs are equal, false otherwise
   */
  private static boolean equalsSigs (Z2Alloy z2alloy, Module module) {
    HashMap<String, Sig> z2alloySigs = new HashMap<String, Sig>(z2alloy.sigmap_);
    HashMap<String, Sig> moduleSigs = new HashMap<String, Sig>();
    for (Sig s : module.getAllSigs()) {
      moduleSigs.put(s.label.replace("this/", ""), s);
    }

    Set<String> keys = new HashSet<String>(z2alloySigs.keySet());
    keys.addAll(moduleSigs.keySet());
    for (String label : keys) {
      if (! equalsSig(z2alloySigs.get(label), moduleSigs.get(label))){
        return false;
      }
    }
    return true;
  }

  
  /**
   * only facts atm are sig facts -> ie sig X{..}{fact}
   * <br>
   * these are represented inside the Module as a list of pairs: this/sig$fact -> fact
   * <br>
   * matches these with the sigfacts in z2alloy by the sig name, then calls equalsExpr on th body on the fact bodies
   * @return true if all facts are equal, false otherwise
  */
  private static boolean equalsFacts (Z2Alloy z2alloy, Module module) {
    HashMap<String, Expr> z2alloyPreds = new HashMap<String, Expr>();
    for (Entry<Sig, Expr> entry : z2alloy.sigfacts_.entrySet()) {
      z2alloyPreds.put(entry.getKey().label, entry.getValue());
    }

    HashMap<String, Expr> modulePreds = new HashMap<String, Expr>();
    for (Pair<String, Expr> entry : module.getAllFacts()) {
      if (entry.a.contains("this/") && entry.a.contains("$fact")) {
        String key = entry.a.replace("this/", "").replace("$fact", "");
        Expr value = entry.b;
        if (entry.b instanceof ExprQuant) value = ((ExprQuant) entry.b).sub;
        modulePreds.put(key, value);
      }
    }
    Set<String> keys = new HashSet<String>(z2alloyPreds.keySet());
    keys.addAll(modulePreds.keySet());

    for (String label : keys) {
      if (! equalsExpr(z2alloyPreds.get(label), modulePreds.get(label))){
        return false;
      }
    }
    return true;
  }

  /**
   * checks  funcs (sigpreds and other functions) for equality<br/>
   * does not check funcs created by Alloy from the body of runs (ie in the form run {...})<br/>
   * removes this/ from the start of funcs<br/>
   * matches funcs by label, then calls equalsFunc on each pair<br/>
   * 
   * @return if all the funcs are equal, false otherwise
   */
  private static boolean equalsFuncs (Z2Alloy z2alloy, Module module) {

    HashMap<String, Func> z2alloyFuncs = new HashMap<String, Func>();
    for (Func f : z2alloy.sigpreds_.values()) {
      z2alloyFuncs.put(f.label, f);
    }
    for (Func f : z2alloy.functions_.values()) {
      z2alloyFuncs.put(f.label, f);
    }

    HashMap<String, Func> moduleFuncs = new HashMap<String, Func>();
    for (Func f : module.getAllFunc()) {
      String key = f.label.replace("this/", "");
      if (f.label.contains("this/run$")) continue;
      moduleFuncs.put(key, f);
    }
    Set<String> keys = new HashSet<String>(z2alloyFuncs.keySet());
    keys.addAll(moduleFuncs.keySet());

    for (String label : keys) {
      if (! equalsFunc(z2alloyFuncs.get(label), moduleFuncs.get(label))){
        return false;
      }
    }
    return true;
  }

  /**
   * two sigs are equal if they are both null or: <br/>
   *    they are both non null<br/>
   *    they have equal labels<br/>
   *    they have the same number of fields<br/>
   *    their fields can be matched up by label, a call to equalExpr is true for all pairs<br/>
   * otherwise it is not equal<br/>
   * 
   * @return true if the sigs are equal, false otherwise
   */
  private static boolean equalsSig (Sig a, Sig b) {
    if (a == null && b == null) return true;
    if (a == null || b == null) return f(a,b);
    if (!equalsString(a.label, b.label)) return f(a,b);
    if (a.getFields().size() != b.getFields().size()) return f(a,b);
    HashMap<String, Field> aFields = new HashMap<String, Field>();
    HashMap<String, Field> bFields = new HashMap<String, Field>();
    for (Field f : a.getFields()) aFields.put(f.label, f);
    for (Field f : b.getFields()) bFields.put(f.label, f);
    Set<String> keys = new HashSet<String>(aFields.keySet());
    keys.addAll(bFields.keySet());
    for (String label : keys) {
      if (! equalsExpr(aFields.get(label), bFields.get(label)))return false;
    }
    return true;
  }

  /**
   * fields are considered equal if they have equal labels, and equalsExpr is true for the sub expression.
   * @return true if the fields are equal, false otherwise
   */
  private static boolean equalsField (Field a, Field b)
  {
    if (!a.label.equals(b.label)) return f(a,b);
    return equalsExpr (((ExprBinary) ((ExprQuant) a.boundingFormula).sub).right,
        ((ExprBinary) ((ExprQuant) b.boundingFormula).sub).right);
  }

  /**
   * expressions are equal if they are both null, or if they are both non null, have the same class, and the call to the equals method
   * defined for the expression type<br/>
   * 
   * expression types currently defined are : ExprUnary, Sig, ExprBinary, ExprList, Field, ExprQuant, ExprVar, ExprCall, ExprConstant.
   * 
   * @return true if the exprs are equal, false otherwise
   */
  private static boolean equalsExpr (Expr a, Expr b)
  {
    if (a == null && b == null) return true;
    if (a == null || b == null) return f(a,b);
    a = strip(a);
    b = strip(b);
    if (a.getClass() != b.getClass()) return f(a,b);
    if (a instanceof ExprUnary) return equalsExprUnary((ExprUnary) a, (ExprUnary) b);
    if (a instanceof Sig) return (equalsString(((Sig) a).label, ((Sig) b).label));
    if (a instanceof ExprBinary) return equalsExprBinary((ExprBinary) a, (ExprBinary) b);
    if (a instanceof ExprList) return equalsExprList((ExprList) a, (ExprList) b);
    if (a instanceof Field) return equalsField((Field) a, (Field) b);
    if (a instanceof ExprQuant) return equalsExprQuant((ExprQuant) a, (ExprQuant) b);
    if (a instanceof ExprVar) return equalsExprVar((ExprVar) a, (ExprVar) b);
    if (a instanceof ExprCall) return equalsExprCall((ExprCall) a, (ExprCall) b);
    if (a instanceof ExprConstant) return equalsExprConstant((ExprConstant) a, (ExprConstant) b);
    throw new RuntimeException(a + " " + b + " " + a.getClass());
  }
  
  /**
   * exprunarys are equal if the ops are the same, and the sub expressions are equal
   * 
   * @return true if the exprunarys are equal, false otherwise
   */
  private static boolean equalsExprUnary(ExprUnary a, ExprUnary b)
  {
    if (a.op != b.op) return f(a,b);
    if (!equalsExpr(a.sub, b.sub)) return f(a,b);
    return true;
  }

  /**
   * exprbinarys are equal if the ops are the same, the left parts of each expression are equal, and the right parts of each expression
   * are equal
   * @return true if the exprbinarys are equal, false otherwise
   */
  private static boolean equalsExprBinary (ExprBinary a, ExprBinary b) {
    if (a.op != b.op) {
      return f(a,b);
    }
    if (!equalsExpr(a.left, b.left) || !equalsExpr(a.right, b.right)) {
      return f(a,b);
    }
    return true;
  }

  /**
   * exprlists are equal if the operation is equal, the number of exprs in the list is equal, and each expr is equal to the expr in 
   * the same position of the other list
   * 
   * the operations are all commutative, but the same exprs in a different order are still considered not equal
   * @return true if the exprlists are equal, false otherwise
   */
  private static boolean equalsExprList(ExprList a, ExprList b)
  {
    if (a.op != b.op) return f(a,b);
    if (a.args.size() != b.args.size()) return f(a, b);
    for (int i = 0; i < a.args.size(); i++) {
      if (! equalsExpr(a.args.get(i), b.args.get(i))) {
        return f(a,b);
      }
    }
    return true;
  }

  /**
   * exprquants are equal if the operation is equal, the number of vars is equal, the vars in each place in the sequence are equal,
   * and the sub expressions are equal
   * 
   * @return true if the exprquants are equal, false otherwise
   */
  private static boolean equalsExprQuant(ExprQuant a, ExprQuant b) {
    if (a.op != b.op) return f(a,b);
    if (a.vars.size() != b.vars.size()) return f(a,b);
    for (int i = 0; i < a.vars.size(); i++) {
      if (!equalsExprVarDecl(a.vars.get(i), b.vars.get(i))) return f(a,b);
    }
    if (! equalsExpr(a.sub, b.sub)) return f(a,b);
    return true;
  }

  /**
   * exprcalls are equal if the numbers of arguments are equal, the arguments are equal, and the label of the function called is equal
   * the the function itself is not checked
   * 
   * @return true if the exprcall is equal, false otherwise
   */
  private static boolean equalsExprCall (ExprCall a, ExprCall b) {
    if (a.args.size() != b.args.size()) return f(a,b);
    for (int i = 0; i < a.args.size(); i++) {
      if (!equalsExpr(a.args.get(i), b.args.get(i))) return f(a,b);
    }
    if (!equalsString(a.fun.label, b.fun.label)) return f(a,b);
    return true;
  }
  
  /**
   * @return true if the exprvar label is equal, false otherwise
   */

  private static boolean equalsExprVar(ExprVar a, ExprVar b)
  {
    if (!equalsString(a.label, b.label)) return f(a,b);
    return true;
  }
  
  
  /**
   * @return true if both the label and expression are equal, false otherwise
   */
  private static boolean equalsExprVarDecl (ExprVar a, ExprVar b) {
    if (!equalsString(a.label, b.label)) return f(a,b);
    if (!equalsExpr(a.expr, b.expr)) return f(a,b);
    return true;
  }

  
  /**
   * two funcs are equal if they are both null, or:<br/>
   *    they have the same label<br/>
   *    the have the same number of parameters<br/>
   *    the parameters in each position in the list are equal<br/>
   *    the return declarations are equal<br/>
   *    the body of the expressions are equal
   *    
   * @return true if the func is equal, false otherwise
   */
  private static boolean equalsFunc(Func a, Func b) {
    if (a == null && b == null) return true;
    if (a == null || b == null) return f(a,b);
    if (!equalsString(a.label, b.label)) return f(a,b);
    if (a.params.size() != b.params.size()) return f(a,b);
    for (int i = 0 ;i < a.params.size(); i++) {
      if (!equalsExprVarDecl(a.params.get(i), b.params.get(i))) return f(a,b);
    }
    if (! equalsExpr(a.returnDecl, b.returnDecl)) return f(a,b);
    if (!equalsExpr(a.getBody(), b.getBody())) return f(a,b);
    return true;
  }

  
  /**
   * 
   * exprconstants are equal if they have the same operation, num (0 if not a number), and string ("" if not a string constant)
   * 
   * @return true if the exprconstants are equal, false otherwise
   */
  private static boolean equalsExprConstant(ExprConstant a, ExprConstant b) {
    if (a.op != b.op) return f(a,b);
    if (a.num != b.num) return f(a,b);
    if (!equalsString(a.string, b.string)) return f(a,b);
    return true;
  }
  
  /**
   * Alloy puts the module sigs/funcs come from before the name. Currently only single module models are used, so they all start with
   * this/
   * 
   * removes this/ from the front of the string before comparison
   */

  private static boolean equalsString(String a, String b) {
    a = a.replace("this/", "");
    b = b.replace("this/", "");
    return a.equals(b);
  }

  
  /**
   * if two things are not equal, it prints the objects and classes to System.err
   */
  private static boolean f(Object a, Object b) {
    String message = a + " != " + b + "\n";
    message += (a == null ? a : a.getClass()) + " !=  " + (b == null ? null :  b.getClass()) + "\n";
    System.err.println(message);
    return false;
  //  throw new RuntimeException(message);
  }
  
  /**
   * Alloy puts some junk in the AST. This strips it out so it matches the Z2Alloy AST
   */

  private static Expr strip(Expr expr)
  {
    if (expr instanceof ExprUnary) {
      ExprUnary exprunary = (ExprUnary) expr;
      if (exprunary.op == ExprUnary.Op.NOOP) { // noops are put in by the alloy parser
        return strip(exprunary.sub);
      }
      if (exprunary.op == ExprUnary.Op.ONEOF) {
        if (exprunary.sub instanceof PrimSig) {
          return strip(exprunary.sub);
        }
        if (exprunary.sub instanceof ExprUnary) {
          return strip(exprunary.sub);
        }
        if (exprunary.sub instanceof ExprQuant) {
          return strip(exprunary.sub);
        }
      }
      if (exprunary.op == ExprUnary.Op.SETOF) { // a relation is always a set
        if (exprunary.sub instanceof ExprBinary) {
          if (((ExprBinary) exprunary.sub).op.toString().contains("->")) {
            return exprunary.sub;
          }
        }
      }
    }
    else if (expr instanceof ExprBinary) {
      ExprBinary exprbinary = (ExprBinary) expr;
      if (exprbinary.left instanceof ExprUnary) {
        ExprUnary exprunary = (ExprUnary) exprbinary.left;
        Expr exprleft = strip(exprunary);
        if (exprleft instanceof PrimSig) {
          PrimSig sig = (PrimSig) exprleft;
          if (sig.label.equals("this")) {
            return strip(exprbinary.right);
          }
        }
        if (exprleft instanceof ExprVar) {
          ExprVar exprvar = (ExprVar) exprleft;
          if (exprvar.label.equals("this")) {
            return strip(exprbinary.right);
          }
        }
      }
    }
    return expr;
  }

}
