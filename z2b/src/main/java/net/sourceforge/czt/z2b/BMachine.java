/**
Copyright 2003, 2006 Mark Utting
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

// the CZT classes for Z.
import net.sourceforge.czt.z.ast.*;

/**
 * This class represents a B abstract machine.
 * It has state variables and operations that manipulate them.
 *
 * Because it is designed for converting Z specs to B, the machine stores
 * Z expressions and predicates etc.  The Z names in the lists and maps
 * are represented as strings, but these may include Z decorations.
 * Operations are specified with pre/postconditions and
 * initialisation is specified with a predicate.
 *
 * @author Mark Utting
 */
public class BMachine
{
  /** The name of the machine */
  protected String name_;

  /** Sets of constants */
  private Map<String,List<String>> sets_ = new HashMap<String,List<String>>();

  /** The constants and their properties */
  private List<String> constants_ = new ArrayList<String>();
  private List<Pred>  properties_ = new ArrayList<Pred>();

  /** Definitions */
  Map<String,Expr> defns_ = new HashMap<String,Expr>();

  /** State variables and their invariants */
  private List<String>  variables_ = new ArrayList<String>();
  List<Pred>  invariant_ = new ArrayList<Pred>();

  /** Initialisation variables and their invariants */
  List<Pred>  initialisation_ = new ArrayList<Pred>();

  List<BOperation> operations_ = new ArrayList<BOperation>();


  /**
   * Constructor for BMachine
   *
   * @param name   The name of the machine.
   */
  public BMachine(String name) {
    name_ = name;
  }


  //=============== Access functions =====================

  /** Returns the sets used in this machine.
   *  The name of each set is mapped to its list of members (DeclNames),
   *  or to null if the set has unknown contents.
   */
  public Map<String,List<String>> getSets() { return sets_; }

  /** Returns the constant 'Name's of this machine. */
  public List<String> getConstants() { return constants_; }

  /** Returns the properties of the constants */
  public List<Pred> getProperties() { return properties_; }

  /** Stores all Name == Expr definitions. */
  public Map<String,Expr> getDefns() { return defns_; }

  /** Returns the state variables of this machine.  They have type Name. */
  public List<String> getVariables() { return variables_; }

  /** Returns the invariant predicates */
  public List<Pred> getInvariant() { return invariant_; }

  /** Returns the initialisation predicates of this machine. */
  public List<Pred> getInitialisation() { return initialisation_; }

  /** Returns the operations of this machine.  They have type BOperation. */
  public List<BOperation> getOperations() { return operations_; }



  /** Prints the machine out to the given file, in *.mch syntax
   *  @param dest  the file where the output should go.
   */
  public void print(BWriter dest) {
    dest.startSection("MACHINE");
    dest.printName(name_);
    if (sets_.size() > 0) {
      dest.continueSection("MACHINE","SETS");
      Iterator<String> i = sets_.keySet().iterator();
      while (i.hasNext()) {
	String n = i.next();
	dest.printName(n);
	List<String> members = sets_.get(n);
	if (members != null) {
	  dest.print(" = {");
	  Iterator<String> mem = members.iterator();
	  while (mem.hasNext()) {
	    dest.printName(mem.next());
	    if (mem.hasNext())
	      dest.print(",");
	  }
	  dest.print("}");
	}
	if (i.hasNext())
	  dest.printSeparator(";");
      }
    }
    if (constants_.size() > 0) {
      dest.continueSection("MACHINE","CONSTANTS");
      printNames(dest,constants_);
    }
    if (defns_.size() > 0) {
      dest.continueSection("MACHINE","DEFINITIONS");
      for (Iterator<Map.Entry<String,Expr>> i = defns_.entrySet().iterator();
           i.hasNext(); ) {
        Map.Entry<String,Expr> entry = i.next();
        dest.beginPrec(BTermWriter.DEFN_PREC);
        dest.printName(entry.getKey());
        dest.print(" == ");
        dest.printExpr(entry.getValue());
        dest.endPrec(BTermWriter.DEFN_PREC);
        if (i.hasNext())
          dest.printSeparator(";");
      }
    }
    if (constants_.size() > 0) {
      assert properties_.size() > 0;
      dest.continueSection("MACHINE","PROPERTIES");
      dest.printPreds(properties_);
    }
    if (variables_.size() > 0) {
      dest.continueSection("MACHINE","VARIABLES");
      printNames(dest,variables_);
      assert invariant_.size() > 0;
      dest.continueSection("MACHINE","INVARIANT");
      dest.printPreds(invariant_);
    }
    dest.continueSection("MACHINE","INITIALISATION");
    if (initialisation_.size() == 0)
      throw new BException("no initialisation predicates");
    // We use:  ANY state' WHERE init' THEN state := state' END
    // Rename outputs to outputs' in the postconditions.
    Map<String,ZName> initRename = new HashMap<String,ZName>();
    for (String name : variables_) {
      initRename.put(name, Create.prime(name));
    }
    dest.printAnyAssign(initRename, initialisation_);
    
    // Now the operations
    if (operations_.size() > 0) {
      dest.continueSection("MACHINE","OPERATIONS");
      Iterator<BOperation> i = operations_.iterator();
      while (i.hasNext()) {
	BOperation op = i.next();
	op.print(dest);
        if (i.hasNext())
          dest.printSeparator(";");
      }
    }
    dest.endSection("MACHINE");
  }


  /** Writes a list of names, separated by commas. */
  //@ requires names != null && names.size() > 0;
  //@ requires dest != null;
  protected void printNames(BWriter dest, List<String> names) {
    Iterator<String> i = names.iterator();
    assert i.hasNext();
    while (true) {
      String n = i.next();
      dest.printName(n);
      if ( ! i.hasNext())
	break;
      dest.printSeparator(",");
    }
  }

  //throw new BException("Z specification must contain one section");
}

