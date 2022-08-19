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
    // the right (e2) depends upon the left (e1),   e1 --> e2
    // the left (e1) supports the right (e2)
    Pair< E, E >p = new Pair< E, E >( e1, e2 );

    //determine whether this pair already exists.
    boolean pairExists = false;
    for (Pair<E,E> pair : dependencies_) {
      if (pair.equals( p )) {
        pairExists = true;
        break;
      }
    }

    if (!pairExists) {
      dependencies_.add( p );
      nodes_.add(e1);
      nodes_.add(e2);
      //System.out.print( "Added: ( " + e1 + "," + e2 + " )" );
    }
  }

  /**
   * Remove direct dependency between two nodes.
   */
  public void remove( E e1, E e2 )
  {
    Pair< E, E >p = new Pair< E, E >( e1, e2 );

    for( Pair< E, E >pair : dependencies_ ) 
    {
      if( pair.equals( p ))
      {
        // found pair to remove
        dependencies_.remove( pair );
//        System.out.println( "Removed (" + pair.left + "," + pair.right + ")" );
        break;
      }
    }
  }


  /**
   * Return the direct dependents of a node.
   */
  public Set<E> getDependents(E e)
  {
    // the right (e2) depends upon the left (e1),   e1 --> e2
    // the left (e1) supports the right (e2)
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
    // the right (e2) depends upon the left (e1),   e1 --> e2
    // the left (e1) supports the right (e2)
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
      if (getSupporters(node).size() != 0) {
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
     throws Exception  // jhr add Exception
  {
//    int b = 0;  // for testing with jdb
    List<E> result = list();    

    Set<E> rootNodes = getRootNodes();
    List<E> queue = list();
    queue.addAll( rootNodes );

    while (queue.size() > 0) 
    {
      int n = 0;
      E next = null;
      while (n < queue.size( )) 
      {
        next = queue.get( n );
        Set<E> supporters = getSupporters( next );
        if (result.containsAll( supporters )) 
        {
          // element can be added to results
          result.add( next );
          queue.remove( n );

          // add element dependents to queue
          Set<E> dependents = getDependents( next );
          for (E e : dependents) 
          {
            if (!queue.contains( e )) 
            {
              queue.add( e );
            }
          }

          // done adding this element
          next = null;

          // because queue is updated, start over
          break;
        }

        n++;
        //        next = queue.get(++n);
      }

      // jhr, check for circular dependencies in queue
      if( true == cyclicDependencyExistsInQueue( queue )) 
      {
//        while( 0 == b ) ; // for testing with jdb
        {
          // We need to do something to escape circular livelock and present 
          // a paletable output to the user.
          throw new Exception( "Dependency graph cyclic chain" );
          // we REALLY need to fix the actual problem; construction of 
          // dependencies has gone wrong sometime earlier (in Checker.java)
          //    See cyclicDependency() solution.
        }
      }
    }

    return result;
  }

  /**
   * @author: jhr
   *
   * <p>
   * Check queue for cyclic dependencies.
   * (Different to checking the dependencies_ set.)
   * </p>
   *
   * <p>
   * When you have "use before definition" the type-checker changes the
   * paragraph ordering so that all variables are defined before use.
   * A similar scenario occurs when you have multiple sections within a
   * document, where the parent definitions are brought in for each using 
   * section. The reordering algorithm in czt can give rise to cyclic 
   * dependencies, which livelock the typechecker.
   *
   * This method checks for cyclic dependencies in the given queue after they 
   * have already been introduced. C.w. cyclicDependencies() below, which checks
   * for cyclic dependencies in the dependency set_ (which is run at the point 
   * of dependency insertion from Checker.java::reorderParaList()).
   * </p>
   *
   * @param queue the List to search
   * @return true if a cyclic dependency exists in queue, else false
   */
  private boolean cyclicDependencyExistsInQueue( List< E >queue )
  {
    boolean result = false;

    if( 0 < queue.size( ))
    {
      List< Pair< E, E >>path = list( );
      int idx = 0;

      // first try to build a path from queue to supporters
      // eg. let queue=[ 6, 7, 8 ], 
      //         6-supporters={ -1, 2, 3, 4, 8 },
      //         7-supporters={ -1, 6 }, 
      //         8-supporters={ -1, 2, 4, 5, 7 }
      //     then path:=[( 6, 8 ),( 7, 6 ),( 8, 7 )]
      while( idx < queue.size( ))
      {
        E elem = queue.get( idx );
        Set< E > supporters = getSupporters( elem );
        for( E el : queue ) 
        {
          if( supporters.contains( el )) 
          {
            path.add( new Pair< E, E >( elem, el ));
          }
        }
        idx++;
      }

      // second, find candidate start nodes, elem on both the left and right
      List< Pair< E, E >> candidate = list( );
      for( Pair< E, E >p : path )
      {
        for( Pair< E, E >q : path )
        {
          if( q.right.equals( p.left ))
          {
            candidate.add( p );
            break;
          }
        }
      }

      // third try walking the path from possible start nodes
      for( Pair< E, E >start : candidate )
      {
        E root = start.left;
        E node = start.right;
        //   start a walk from the root node, and see if we can get back to the
        //   root following the path node by node
        //   from the above example, walk=( 6, 8 ),( 6, 7 ),( 6, 6 )!
        idx = 0;
        while(( idx < path.size( ))&&( false == result ))
        {
          for( Pair< E, E >next : path )
          {
            if( next.left.equals( node ))
            {
              node = next.right;
            }
            if( node.equals( root ))
            {
              result = true;
              break;
            }
          }
          idx++;
        }
      }
    }

    return result;
  }

  /**
   * @author: jhr
   *
   * <p>
   * Check for cyclic dependencies in dependency_set.
   * (Different to checking a List as per cyclicDependencyExistsInQueue.)
   * Called from Checker.java::reorderParaList
   * </p>
   *
   * <p>
   * When you have "use before definition" the type-checker changes the
   * paragraph ordering so that all variables are defined before use.
   * A similar scenario occurs when you have multiple sections within a
   * document, where the parent definitions are brought in for each using 
   * section. Adding dependencies in Checker.java::reorderParaList can give 
   * rise to cyclic dependencies. 
   * (Checker.java::addDependency doesn't seem to generate cyclic dependencies;
   * in the test cases run.)
   * </p>
   *
   * @return true if a cyclic dependency exists in dependencies_, else false
   */
  public boolean cyclicDependencies( )
  {
    boolean result = false;

    // find candidate start nodes, elem on both the left and right
    List< Pair< E, E >> candidate = list( );
    for( Pair< E, E >p : dependencies_ )
    {
      for( Pair< E, E >q : dependencies_ )
      {
        if( q.right.equals( p.left ))
        {
          candidate.add( p );
          break;
        }
      }
    }

    // try walking the path from each possible start node looking for the same
    // start node = recursive cycle
    for( Pair< E, E >start : candidate )
    {
      Pair< E, E >root = null;
      Pair< E, E >livelock = new Pair< E, E >( start.left, start.left );

      root = findCyclic( start.left, start, 0 );
      if( null != root )
      {
        if( root.equals( livelock ))
        {
//          System.out.println( "cd trapped cyclic livelock" );
        }
        else
        {
//          System.out.println( "cd root: (" + root.left + "," + root.right + ")" );
        }
        result = true;
        break;
      }
    }

    return result;
  }

  /**
   * @author: jhr
   *
   * <p>
   * Recursively search dependencies_ for a start node
   * </p>
   **/
  private Pair< E, E > findCyclic( E start, Pair< E, E >pair, int depth )
  {
    Pair< E, E >result = null;

//    System.out.println( "fc1: (" + pair.left + "," + pair.right + ") Goal = " + start );

    if( depth > dependencies_.size( ))
    {
      result = new Pair< E, E >( start, start );  // a non-null value to unwrap
    }
    else
    if( pair.right.equals( start ))
    {
      result = pair;
//      System.out.println( "fc2: (" + pair.left + "," + pair.right + ")" );
    }
    else
    {
      for( E e : getDependents( pair.right ))
      {
        if( !(( e.equals( -1 ))||( e.equals( 0 ))))  // shouldn't be any
        {
          Pair< E, E >p = new Pair< E, E >( pair.right, e );
          result = findCyclic( start, p, depth + 1 );
          if( null != result )
          {
            break;
          }
        }
      }
    }

    return( result );
  }

  /**
   * @author: jhr
   *
   * <p>
   * Remove root dependency in cyclic dependency
   * Called from Checker.java::reorderParaList
   * </p>
   *
   * <p>
   * Find the root of a path leading to the cyclic dependency pair ( src, dst )
   * and remove that root.
   * Ensure there is a path from the section to the cyclic dependency pair.right
   * so that element is not left dangling in the dependency_ set.
   * </p>
   *
   * @param sect the "node" to re-connect the dst of a cut root pair 
   *             (nominally the current paragraph section, sectTypeEnv())
   *        src the source node of a dependency arc
   *        dst the destination node of a dependency arc
   */
  public void removeRootSupporter( E sect, E src, E dst )
  {
    Pair< E, E >root = null;
    Pair< E, E >start = new Pair< E, E >( src, dst );

    root = findCyclicReverse( dst, start );
    if( null != root )
    {
//      System.out.println( "rRS root:(" + root.left + "," + root.right + ")" );
      remove( root.left, root.right );

      if( 0 == getSupporters( root.right ).size( ))
      {
        // ensure there is a path to next.right from the current sectTypeEnv()
        // so it is not left dangling in the dependency_ set.
        // most (all?) dependency_ sets already have a path to next.right anyway
        Pair< E, E >p = new Pair< E, E >( sect, root.right );
        dependencies_.add( p );
      }
    }
  }

  /**
   * @author: jhr
   *
   * <p>
   * Recursive backward search dependencies_ for an end node
   * </p>
   **/
  private Pair< E, E > findCyclicReverse( E end, Pair< E, E >pair )
  {
    Pair< E, E >result = null;

//    System.out.println( "fcr1: (" + pair.left + "," + pair.right + ") Goal = " + end );

    if( pair.left.equals( end ))
    {
      result = pair;
//      System.out.println( "fcr2: (" + pair.left + "," + pair.right + ")" );
    }
    else
    {
      for( E e : getSupporters( pair.left ))
      {
        if( !(( e.equals( -1 ))||( e.equals( 0 ))))
        {
          Pair< E, E >p = new Pair< E, E >( e, pair.left );
          result = findCyclicReverse( end, p );
          if( null != result )
          {
            break;
          }
        }
      }
    }

    return( result );
  }

  public void dump()
  {
    dumpDependencies( "digraph" );
  }

  public void dumpDependencies( String src )
  {
    System.out.print( src + " ={");
    for( Pair< E, E >pair : dependencies_ )
    {
      System.out.print( "( " + pair.left + "," + pair.right + " )," );
    }
    System.out.println("}");
  }

  public void dump_q( List< E >queue )
  {
    int idx = 0;
    E elem = null;
    Set<E> s = null;

    System.out.println("dependencies={");
    while( idx < queue.size( ))
    {
      elem = queue.get( idx );
      System.out.println( "\t" + idx + "\t" + elem );
      s = getSupporters( elem );
      System.out.println( "\t\tsupporters = " + s );
      s = getDependents( elem );
      System.out.println( "\t\tdependents = " + s );
      idx++;
    }
    System.out.println("}");
  }

  public void dump_q_path( List< E >queue )
  {
    if( 0 < queue.size( ))
    {
      List< Pair< E, E >> path = list( );
      int idx = 0;

      // first try to build a path from queue to supporters
      while( idx < queue.size( ))
      {
        E elem = queue.get( idx );
        Set< E > supporters = getSupporters( elem );
        for( E el : queue ) 
        {
          if( supporters.contains( el )) 
          {
            path.add( new Pair< E, E >( elem, el ));
          }
        }
        idx++;
      }

      // dump path
      System.out.print( "path={");
      for( Pair< E, E >pair : path ) 
      {
        System.out.print( "( " + pair.left + "," + pair.right + " )," );
      }
      System.out.println("}");


      // second, find candidate start nodes, elem on both the left and right
      List< Pair< E, E >> candidate = list( );
      for( Pair< E, E >p : path )
      {
        for( Pair< E, E >q : path )
        {
          if( q.right.equals( p.left ))
          {
            candidate.add( p );
            break;
          }
        }
      }

      // dump candidates
      System.out.print( "candidates={");
      for( Pair< E, E >pair : candidate ) 
      {
        System.out.print( "( " + pair.left + "," + pair.right + " )," );
      }
      System.out.println("}");
    }
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
