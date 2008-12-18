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

  public static boolean equals(Z2Alloy z2alloy, Module module)
  {
    return equalsSigs(z2alloy, module) && equalsFacts(z2alloy, module) && equalsFuncs(z2alloy, module);
  }

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

  private static boolean equalsFacts (Z2Alloy z2alloy, Module module) {
    // only facts atm are sig facts -> ie sig X{..}{fact}
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

  private static boolean equalsField (Field a, Field b)
  {
    if (!a.label.equals(b.label)) return f(a,b);
    return equalsExpr (((ExprBinary) ((ExprQuant) a.boundingFormula).sub).right,
        ((ExprBinary) ((ExprQuant) b.boundingFormula).sub).right);
  }

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
  private static boolean equalsExprUnary(ExprUnary a, ExprUnary b)
  {
    if (a.op != b.op) return f(a,b);
    if (!equalsExpr(a.sub, b.sub)) return f(a,b);
    return true;
  }

  private static boolean equalsExprBinary (ExprBinary a, ExprBinary b) {
    if (a.op != b.op) return f(a,b);
    if (!equalsExpr(a.left, b.left) || !equalsExpr(a.right, b.right)) return f(a,b);
    return true;
  }

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

  private static boolean equalsExprQuant(ExprQuant a, ExprQuant b) {
    if (a.op != b.op) return f(a,b);
    if (a.vars.size() != b.vars.size()) return f(a,b);
    for (int i = 0; i < a.vars.size(); i++) {
      if (!equalsExprVarDecl(a.vars.get(i), b.vars.get(i))) return f(a,b);
    }
    if (! equalsExpr(a.sub, b.sub)) return f(a,b);
    return true;
  }

  private static boolean equalsExprCall (ExprCall a, ExprCall b) {
    if (a.args.size() != b.args.size()) return f(a,b);
    for (int i = 0; i < a.args.size(); i++) {
      if (!equalsExpr(a.args.get(i), b.args.get(i))) return f(a,b);
    }
    if (!equalsString(a.fun.label, b.fun.label)) return f(a,b);
    return true;
  }


  private static boolean equalsExprVar(ExprVar a, ExprVar b)
  {
    if (!equalsString(a.label, b.label)) return f(a,b);
    return true;
  }
  
  private static boolean equalsExprVarDecl (ExprVar a, ExprVar b) {
    if (!equalsString(a.label, b.label)) return f(a,b);
    if (!equalsExpr(a.expr, b.expr)) return f(a,b);
    return true;
  }

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

  private static boolean equalsExprConstant(ExprConstant a, ExprConstant b) {
    if (a.op != b.op) return f(a,b);
    if (a.num != b.num) return f(a,b);
    if (!equalsString(a.string, b.string)) return f(a,b);
    return true;
  }

  private static boolean equalsString(String a, String b) {
    a = a.replace("this/", "");
    b = b.replace("this/", "");
    return a.equals(b);
  }

  private static boolean f(Object a, Object b) {
    String message = a + " != " + b + "\n";
    message += (a == null ? a : a.getClass()) + " !=  " + (b == null ? null :  b.getClass()) + "\n";
    System.err.println(message);
//    return false;
  throw new RuntimeException(message);
  }

  private static Expr strip(Expr expr)
  {
    if (expr instanceof ExprUnary) {
      ExprUnary exprunary = (ExprUnary) expr;
      if (exprunary.op == ExprUnary.Op.NOOP) {
        return strip(exprunary.sub);
      }
      if (exprunary.op == ExprUnary.Op.ONEOF) {
        if (exprunary.sub instanceof PrimSig) {
          return strip(exprunary.sub);
        }
        if (exprunary.sub instanceof ExprUnary) {
          return strip(exprunary.sub);
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
