/*
 * EnvirNew.java
 *
 * Created on 07 April 2005, 12:56
 */

package net.sourceforge.czt.animation.eval;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/**
 *
 * @author leo
 */
public class EnvirUtils {
    
    /** Creates a new instance of EnvirNew */
    private EnvirUtils() {        
    }
    
    public static Envir copy(Envir a) {
        ArrayList<ZName> n = new ArrayList<ZName>();
        ArrayList<Expr> e = new ArrayList<Expr>();
        Envir result = new Envir();
        Envir env = a;
        while (env != null) {
            if (env.name_ != null) {
                n.add(env.name_);
                e.add(env.expr_);
            }
            env = env.nextEnv;
        }
        assert n.size() == e.size();
        ListIterator<ZName> li = n.listIterator(n.size());
        ListIterator<Expr> lj = e.listIterator(e.size());
        while (li.hasPrevious() && lj.hasPrevious()) {
            ZName name = li.previous();
            Expr expr = lj.previous();
            result = result.plus(name, expr);
        }
        return result;
    }
    
    // override merge
    public static Envir merge(Envir a, Envir b) {
        Envir result = copy(a);
        Envir env = b;
        while (env != null) {
            if (env.name_ != null && !result.isDefined(env.name_)) {
                result = result.plus(env.name_, env.expr_);
            }
            env = env.nextEnv;
        }
        return result;
    }
    
    public static boolean subset(Envir one, Envir other) {
        Envir env = one;
        while (env != null) {
            if (env.name_ != null && !other.isDefined(env.name_))
                return false;
            env = env.nextEnv;
        }
        return true;
    }
    
    public static boolean disjoint(Envir one, Envir other) {
        Envir env = other;
        while (env != null) {
            // If this Envir has defined name from other Envir then they are not disjoint.
            if (env.name_ != null && one.isDefined(env.name_))
                return false;
            env = env.nextEnv;
        }
        return true;
    }
    
    public static Set<ZName> names(Envir one) {
        Set<ZName> result = new HashSet<ZName>();
        Envir env = one;
        while (env != null) {
            if (one.name_ != null)
                result.add(one.name_);
            env = env.nextEnv;
        }
        return result;
    }
    
    public static List<Expr> exprs(Envir one) {
        List<Expr> result = new ArrayList<Expr>();
        Envir env = one;
        while (env != null) {
            if (one.name_ != null)
                result.add(one.expr_);
            env = env.nextEnv;
        }
        return result;
    }
    
    public static boolean sameAs(Envir one, Envir other) {
        return names(one).equals(names(other)) && exprs(one).equals(exprs(other));
    }    
}
