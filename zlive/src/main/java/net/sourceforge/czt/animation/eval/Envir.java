/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval;

import java.util.HashSet;
import java.util.Set;

import net.sourceforge.czt.animation.eval.result.EvalResult;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/** An Environment is conceptually a mapping from variable names
    (ZName) to values (Expr).
    However, it can also contain additional information about each
    name, such as type information.  This data structure is designed
    to allow environments to be extended in a non-destructive way.
    This is why add() returns a new environment.
    
    TODO: think more about the semantics of the equals.  Should the
    order matter?  Should duplicate names matter?  
    But is equals used anywhere, apart from unit tests?
*/
public class Envir
{
  /** When 'expr_' is set to this unique value it means that 'name_' is hidden. */
  private static final EvalResult hiddenValue = new EvalResult() {};
  
  protected Envir nextEnv;
  // An empty environment always has name==null && term==null;
  protected ZName name_;
  protected Expr expr_;

  /** Create an empty Envir */
  public Envir()
  {
  }

  /** Lookup the value of a name in the Environment.
   * @throws EvalException if want is not defined in this environment.
   * @return The value may be null.
   */
  //@ requires isDefined(want);
  public/*@pure@*/Expr lookup(/*@non_null@*/ZName want) {
    Envir env = this;
    while (env != null) {
      if (sameName(want, env.name_)) {
    	if (env.expr_ == hiddenValue) {
    	    throw new EvalException("Hidden name in envir: " + want);
    	}
        return env.expr_;
      }
      env = env.nextEnv;
    }
    throw new EvalException("Missing name in envir: " + want);
  }

  public static boolean sameName(/*@non_null@*/ZName a, ZName b) {
    // TODO make this equals test more elegant.  
    // Must avoid differences just because of the decl_ field.
    return b != null 
        && a.getWord().equals(b.getWord())
        && a.getStrokeList().equals(b.getStrokeList());
  }

  /** Return the set of newly defined names. */
  public /*@pure@*/ Set<ZName> definedSince(/*@non_null@*/Envir env0)
  {
    Set<ZName> result = new HashSet<ZName>();
    Set<ZName> hiddenNames = null;
    Envir env = this;
    while (env != null && env != env0) {
      if (env.name_ != null) {
    	if (env.expr_ == hiddenValue) {
    	  if (hiddenNames == null) {
    		hiddenNames = new HashSet<ZName>();
    	  }
    	  hiddenNames.add(env.name_);
    	} else {
    	  result.add(env.name_);
    	}
      }
      env = env.nextEnv;
    }
    if (hiddenNames != null) {
      result.removeAll(hiddenNames);
    }
    return result;
  }

  private Set<ZName> plusHiddenName(Set<ZName> hidden, ZName name) {
  	if (hidden == null) {
  		hidden = new HashSet<ZName>();
  	}
  	hidden.add(name);
  	return hidden;
  }

  /** See if a name is recently defined in the Environment.
   *  
   *  @return true if the name is defined in this environment, but not in env0.
   */
  public /*@pure@*/ boolean isDefinedSince(
      /*@non_null@*/Envir env0,
      /*@non_null@*/ZName want) {
    Envir env = this;
    Set<ZName> hiddenNames = null;
    while (env != null && env != env0) {
      if (env.expr_ == hiddenValue) {
    	hiddenNames = plusHiddenName(hiddenNames, env.name_);
      }
      if (sameName(want, env.name_))
        return hiddenNames == null || !hiddenNames.contains(want);
      env = env.nextEnv;
    }
    return false;
  }

  //TODO: just call isDefinedSince(null)?
  
  /** See if a name is defined in the Environment. 
  @return true if the name exists, false if it does not exist.
  */
 public/*@pure@*/boolean isDefined(/*@non_null@*/ZName want) {
   Envir env = this;
   Set<ZName> hiddenNames = null;
   while (env != null) {
	 if (env.expr_ == hiddenValue) {
	   hiddenNames = plusHiddenName(hiddenNames, env.name_);
	 }
     if (sameName(want, env.name_))
         return hiddenNames == null || !hiddenNames.contains(want);
     env = env.nextEnv;
   }
   return false;
 }

  /** Update the value of a name in the Environment. 
      WARNING: this destructively changes the Environment
      and may change other environments that share parts of this environment.
     @param name This name must already exist in the environment.
     @param newvalue The new value for name.
  */
 //@ requires isDefined(name); 
  public void setValue(/*@non_null@*/ZName name,
      				   /*@non_null@*/Expr newvalue) {
    Envir env = this;
    while (env != null) {
      if (sameName(name, env.name_)) {
    	if (env.expr_ == hiddenValue){
   	      throw new EvalException("illegal Envir setValue hidden: "+name+"="+newvalue);
    	}
        env.expr_ = newvalue;
        return;
      }
      env = env.nextEnv;
    }
    // we should not be setting the value of an undefined name!
    throw new EvalException("illegal Envir setValue: "+name+"="+newvalue);
  }

  /** Create a new Envir which equals this one, plus an extra name,value pair.
   *  It is quite common to set the value to null, which means that
   *  the actual value of that name will be set later, using the 
   *  setValue method.  Typically, the name,value pair is created
   *  once, then setValue is used to give the name many different
   *  values during the search for a solution to some predicate.
   *  
   *  @param  name  The name to add.
   *  @param  value The value to which name will be bound.  Can be null.
   *  @return The new extended environment
  */
  public Envir plus(/*@non_null@*/ZName name, Expr value)
  {
    Envir result = new Envir();
    result.nextEnv = this;
    result.name_ = name;
    result.expr_ = value;
    return result;
  }

  /** Creates an environment which extends this one by adding
   *  all the name==expr pairs in binding.
   */
  public Envir plusAll(BindExpr binding)
  {
    Envir result = this;
    for (Decl decl : binding.getZDeclList()) {
      ConstDecl cdecl = (ConstDecl) decl;
      result = result.plus(cdecl.getZName(), cdecl.getExpr());
    }
    return result;
  }

  /**
   * Hides the given name, so the the environment *appears* not to include that name.
   *
   * @param name
   * @return
   */
  public Envir hide(ZName name) {
	return plus(name, hiddenValue);
  }

  @Override
  public int hashCode()
  {
    assert false : "Envir.hashCode() not implemented.";
    return 42;
  }

  /** Two environments are equal if they contain the same names
      and values, in exactly the same order.
  */
  public boolean equals(Object obj)
  {
    // assert false : "Envir.equals() should not be used?";
    if ( ! (obj instanceof Envir))
      return false;
    Envir e2 = (Envir)obj;

    //System.out.println("equals: name="+name+", e2.name_="+e2.name_);
    if (name_==null) {
      if (e2.name_ != null)
        return false;
    } else {
      if (! sameName(name_, e2.name_))
        return false;
    }

    //System.out.println("equals: expr_="+expr_+", e2.expr_="+e2.expr_);
    if (expr_==null) {
      if (e2.expr_ != null)
        return false;
    } else {
      if (! expr_.equals(e2.expr_))
        return false;
    }

    //System.out.println("equals: nextEnv="+nextEnv+", e2.nextEnv="+e2.nextEnv);
    if (nextEnv==null) {
      if (e2.nextEnv != null)
        return false;
    } else {
      if (!nextEnv.equals(e2.nextEnv))
        return false;
    }

    return true;
  }

  public String toString() {
    StringBuffer result = new StringBuffer();
    result.append("Envir{");
    Envir env = this;
    while (env != null) {
      env.pairToString(result);
      result.append(", ");
      env = env.nextEnv;
    }
    result.append("}");
    return result.toString();
  }

  protected void pairToString(StringBuffer result) {
	if (expr_ == hiddenValue) {
	  result.append("HIDE ");
	  result.append(name_);
	} else {
	  result.append(name_);
      result.append("=");
      // truncate multi-line values, so output is not TOO verbose.
      String es = "";
      if (expr_ != null) {
        es = expr_.toString();
        final int nl = es.indexOf('\n');
        if (nl >= 0) {
          es = es.substring(0, nl) + "...";
        }
      }
    result.append(es);
	}
  }
  
  /** Returns a copy of this environment, with no values shared.
   *  This is sometimes necessary when an expression with free variables
   *  (eg. SetComp) is being passed outside of its scope, so the value 
   *  of those variables needs to be copied and frozen.
   */
  public Envir deepCopy()
  {
    Envir result = new Envir();
    Envir src = this;
    Envir tail = result; // the last node (so far) of the cloned list.
    tail.expr_ = src.expr_;
    tail.name_ = src.name_;
    while (src.nextEnv != null) {
      // invar: tail is non-null and its name_ and expr_ fields are
      // a copy of src, but its nextEnv field must be copied from src.nextEnv.
      tail.nextEnv = new Envir();
      tail = tail.nextEnv;
      src = src.nextEnv;
      tail.name_ = src.name_;
      tail.expr_ = src.expr_;
    }
    return result;
  }
}
