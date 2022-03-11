/*
  Copyright (C) 2004 Tim Miller
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.typecheck.z.util;

import java.util.Set;
import java.util.List;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

/**
 * Track dependencies between nodes.
 */
public class DependencyGraph<E> {

  //the set of nodes in the graph
  protected Set<E> nodes_;

  //the set of direct dependencies in the DMS
  protected Set<Pair<E,E>> dependencies_;

  public DependencyGraph()
  {
    dependencies_ = set();
    nodes_ = set();
  }

  /**
   * Adds a direct dependencies between two nodes.
   */
  public void add(E e1, E e2)
  {
    //determine whether this pair already exists.
    boolean pairExists = false;
    for (Pair<E,E> pair : dependencies_) {
      if (pair.equals(new Pair<E,E>(e1, e2))) {
	pairExists = true;
	break;
      }
    }

    if (!pairExists) {
      dependencies_.add(new Pair<E,E>(e1, e2));
      nodes_.add(e1);
      nodes_.add(e2);
    }
  }

  /**
   * Return the direct dependents of a node.
   */
  public Set<E> getDependents(E e)
  {
    Set<E> result = set();

    for (Pair<E,E> pair : dependencies_) {
      if (e.equals(pair.left)) {
	result.add(pair.right);
      }
    }

    return result;
  }

  /**
   * Return the set of supporting nodes for a node.
   */
  public Set<E> getSupporters(E e)
  {
    Set<E> result = set();

    for (Pair<E,E> pair : dependencies_) {
      if (e.equals(pair.right)) {
	result.add(pair.left);
      }
    }

    return result;
  }

  /**
   * Returns the set of transitive supporters of a node.
   */
  public Set<E> getTransitiveSupporters(E e)
  {
    Set<E> result = set();

    Set<E> supporters = getSupporters(e);
    result.addAll(supporters);

    for (E s : supporters) {
      Set<E> transitive = getTransitiveSupporters(s);
      result.addAll(transitive);
    }

    return result;
  }

  /**
   * Return the set of root nodes.
   */
  public Set<E> getRootNodes()
  {
    Set<E> result = set();

    for (E node : nodes_) {
      if (getSupporters(node).size() == 0) {
	result.add(node);
      }
    }

    return result;
  }

  /**
   * Returns a list of all nodes derived using a modified
   * breadth-first search.  In the CZT typechecker, this is used to
   * re-order paragraphs to allow use before declaration. The
   * modification to standard breadth-first search is that a node is
   * only added to the result if all of its supporters (parents) have
   * been added to the result.
   */
  public List<E> bfs()
  {
    List<E> result = list();    

    Set<E> rootNodes = getRootNodes();

    List<E> queue = list();
    queue.addAll(rootNodes);

    while (queue.size() > 0) {
      int n = 0;
      E next = null;
      while (n < queue.size()) {
	next = queue.get(n);
	Set<E> supporters = getSupporters(next);
	if (result.containsAll(supporters)) {
	  result.add(next);
	  queue.remove(n);
	  break;
	}
	n++;
	//        next = queue.get(++n);
      }

      Set<E> dependents = getDependents(next);
      for (E e : dependents) {
	if (!queue.contains(e)) {
	  queue.add(e);
	}
      }
    }

    return result;
  }

  public void dump()
  {
    System.out.println("digraph {");
    for (Pair<E,E> pair : dependencies_) {
      System.out.println("\t" + pair.left + " -> " + pair.right);
    }
    System.out.println("}");
  }

  /**
   *  The pair objects to be used for the set of dependencies
   */
  protected class Pair<K,F>
  {
    //the left and right elements of the pair
    public K left;
    public F right;

    public Pair(K left, F right) {
      this.left = left;
      this.right = right;
    }

    public boolean equals(Object o)
    {
      if (o != null && o instanceof Pair)
      {
    	@SuppressWarnings("unchecked")
    	Pair<K,F> p = (Pair<K,F>)o;
    	return (p.left.equals(left) && p.right.equals(right));
      }
      return false;
    }
    
    public int hashCode()
    {
    	int h = super.hashCode();
    	h += left.hashCode();
    	h += right.hashCode();
    	return h;
    }

    public String toString() {
      return ("(" + left + ", " + right + ")");
    }
  }
}
