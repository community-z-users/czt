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
import net.sourceforge.czt.z.ast.RefName;

/**
 *
 * @author leo
 */
public class EnvirUtils {
    
    /** Creates a new instance of EnvirNew */
    private EnvirUtils() {        
    }
    
    public static Envir copy(Envir a) {
        ArrayList n = new ArrayList();
        ArrayList e = new ArrayList();
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
        for(ListIterator li = n.listIterator(n.size()),
                         lj = e.listIterator(e.size());
                li.hasPrevious() && lj.hasPrevious(); ) {
            RefName name = (RefName)li.previous();
            Expr expr = (Expr)lj.previous();
            result = result.add(name, expr);
        }
        return result;
    }
    
    // override merge
    public static Envir merge(Envir a, Envir b) {
        Envir result = copy(a);
        Envir env = b;
        while (env != null) {
            if (env.name_ != null && !result.isDefined(env.name_)) {
                result = result.add(env.name_, env.expr_);
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
    
    public static Set names(Envir one) {
        Set result = new HashSet();
        Envir env = one;
        while (env != null) {
            if (one.name_ != null)
                result.add(one.name_);
            env = env.nextEnv;
        }
        return result;
    }
    
    public static List exprs(Envir one) {
        List result = new ArrayList();
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
