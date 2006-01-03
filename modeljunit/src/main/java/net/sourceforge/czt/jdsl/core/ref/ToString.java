/*
  Copyright (c) 1999, 2000 Brown University, Providence, RI
  
                            All Rights Reserved
  
  Permission to use, copy, modify, and distribute this software and its
  documentation for any purpose other than its incorporation into a
  commercial product is hereby granted without fee, provided that the
  above copyright notice appear in all copies and that both that
  copyright notice and this permission notice appear in supporting
  documentation, and that the name of Brown University not be used in
  advertising or publicity pertaining to distribution of the software
  without specific, written prior permission.
  
  BROWN UNIVERSITY DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
  SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR ANY PARTICULAR PURPOSE.  IN NO EVENT SHALL BROWN
  UNIVERSITY BE LIABLE FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL
  DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
  PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER
  TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
  PERFORMANCE OF THIS SOFTWARE.
*/

package net.sourceforge.czt.jdsl.core.ref;

import net.sourceforge.czt.jdsl.core.api.*;
import java.io.*;

/**
 * Collection of static methods
 * that generate a string representing a container or accessor.  Since
 * all the useful methods are static, it should never be necessary to
 * create an instance of ToString.
 * <p>
 * Every stringfor(.) method that takes a container type comes in
 * two flavors:  a default and one parametrized for how to stringify
 * an accessor.  The former is used in the toString() method of the
 * applicable containers.  The latter may be used if you want more
 * or less information about each accessor than the default gives.
 * <p>
 * Since it is not possible to guarantee a snapshot of
 * a given container when many threads are running (unless the
 * container is synchronized), the stringfor(.) methods
 * cannot guarantee snapshot semantics for output.
 *
 * @author Keith Schmidt
 * @author Mark Handy
 * @version JDSL 2.1.1 
 */

public class ToString {

    // need never instantiate a ToString; just use static methods
    private ToString() {}




  /**
   * Way to parametrize the stringifying of a position, within the
   * stringifying of a container. For instance, you
   * could write the position's address, or some introductory string
   * and then the element, or just the element.
   * @see ToString.PositionWritesElementOnly
   */   
  public static interface PositionToString {
    String stringfor( Position pos );
  }
    
  /**
   * Way to parameterize the stringifying of a locator, within the
   * stringifying of a container.  For instance, you could write the
   * locator's address, or some introductory string and then the key,
   * or just the key, or the key and the element.
   * @see ToString.LocatorCollectionsStyle
   */
  public static interface LocatorToString {
    String stringfor( Locator loc );
  }



    
    // constant instantiations of the interfaces above, to implement
    // default stringfor(.) methods
    public static final PositionToString pos_to_element_s =
    new PositionWritesElementOnly();
    
    public static final LocatorToString loc_to_collections_style_s =
    new LocatorCollectionsStyle();

    // array of space characters, for variable indentation when
    // stringifying trees
    private static byte[] spaces = null;



    
    
    /** 
     * Gives string representation of a sequence, parameterized by how
     * to represent each position (i.e., constructs a string by
     * iterating over all positions of the sequence, concatenating the
     * specified string representation of each position).  Iteration
     * is in the natural order for a sequence.
     *
     * @param s sequence to stringify
     * @param pts how to stringify each position
     * @return the string representation of s
     */
    public static String stringfor( InspectableSequence s,
				    PositionToString pts ) {
	String toReturn = "[";
	PositionIterator pp = s.positions();
	//first element should have no comma
	if( pp.hasNext() ) toReturn += " " + pts.stringfor( pp.nextPosition() );
	while( pp.hasNext() ) {
	    toReturn += ", " + pts.stringfor( pp.nextPosition() );
	}
	toReturn += " ]";
	return toReturn;
    }
    
    /** 
     * Default version of stringfor( InspSeq, PTS ).  Each position is stringified
     * with the string representation of its element only.
     */
     public static String stringfor( InspectableSequence s ) {
	return stringfor( s, pos_to_element_s );
     }

    





    /** 
     * Recursively dumps a byte representation of a subtree onto a
     * stream.  Used by stringfor( InspTree ).  Publicly available in
     * case you want to stringify a subtree and really think this way
     * is less work than doing it yourself.  You'll want to make sure
     * the "spaces" static variable is initialized first :)
     * @param subtreeRoot root of subtree to represent
     * @param pts way to stringify each position
     * @param ostream stream on which to represent the subtree
     * @param t tree, so children(.) can be called
     * @param indentation number of spaces to indent this level
     * @param indentation_increment amount by which indentation will
     * be increased before writing children
     */
    public static void writeNodeAndChildren( Position subtreeRoot,
					     PositionToString pts,
					     DataOutputStream ostream,
					     InspectableTree t,
					     int indentation,
					     int indentation_increment) {
	try {
	    // indent, then write the subtreeRoot
	    ostream.write( spaces, 0, indentation );
	    ostream.writeBytes( pts.stringfor(subtreeRoot) );
	    ostream.writeBytes( "\n" );
	} catch( java.io.IOException e ) {
	    System.err.println( "\nAn I/O error occurred: " + e );
	    return;
	}
	PositionIterator pp = t.children( subtreeRoot );
	// recur on all children
	while( pp.hasNext() ) writeNodeAndChildren( pp.nextPosition(),
						    pts,
						    ostream,
						    t,
						    indentation + indentation_increment,
						    indentation_increment);
    }
    
    /** 
     * Gives string representation of a tree, parametrized by how to represent
     * each position.  It does a preorder traversal, giving a newline and
     * some indentation before each node, then represents each node
     * as specified. It can print a tree which is at most 100 levels deep.
     *
     * @param t tree to stringify
     * @param pts how to stringify each position
     * @throws IndexOutOfBoundsException if the tree is more then 100 levels deep
     * @return the string representation of t
     */
    public static String stringfor( InspectableTree t, PositionToString pts ) {
	if( spaces==null ) {
	    spaces = new byte[200]; // tree can't be more than 100 levels deep
	    for( int i=0; i<200; ++i ) spaces[i] = (byte)' ';
	}
	// the 4 below was generated entirely at random
	ByteArrayOutputStream bstr = new ByteArrayOutputStream( t.size() * 4 );
	DataOutputStream ostr = new DataOutputStream( bstr );
	writeNodeAndChildren( t.root(), pts, ostr, t, 0, 2 );
	return bstr.toString();
    }
    
    /** 
     * Default version of stringfor( InspTree, PTS ).  Each position is stringified
     * with the string representation of its element only.
     */
    public static String stringfor( InspectableTree t ) {
	return stringfor( t, pos_to_element_s );
    }
    



    /** 
     * Gives string representation of a dictionary or priority queue,
     * parameterized by how to represent 
     * each locator (i.e., constructs a string by iterating over all locators
     * of the container, concatenating the specified string representation
     * of each locator).  Iteration is in whatever order the container's locators()
     * method provides.
     * 
     * @param k key-based container to stringify
     * @param lts how to stringify each locator
     * @return  the string representation of k
     */
     public static String stringfor( InspectableKeyBasedContainer k,
				    LocatorToString lts ) {
	String toReturn = "{";
	LocatorIterator pl = k.locators();
	// first element should have no comma
	if ( pl.hasNext() ) toReturn += " " + lts.stringfor( pl.nextLocator() );
	while ( pl.hasNext() ) { 
	    toReturn += ", " + lts.stringfor( pl.nextLocator() );
	}
	toReturn += " }";
	return toReturn;
    }

    /** 
     * Default version of stringfor( InspKBC, LTS ).  Each locator is stringified
     * in the Java Collections style: (key)=(element).
     */
     public static String stringfor( InspectableKeyBasedContainer k ) {
	return stringfor( k, loc_to_collections_style_s );
     }



    

    /* commented out pending some thought about how to stringify
       an iterator without changing its state -- for now, you gotta
       write you own toString() inside the iterator
       
    public static String stringfor( ObjectIterator it ) {
	String toReturn = "(";
	// first element is not preceded by a comma
	if( it.hasNext() ) toReturn += " " + it.nextObject();
	while( it.hasNext() ) toReturn += ", " + it.nextObject();
	toReturn += " )";
	it.reset();
	return toReturn;
    }

    public static String stringfor( PositionIterator it, PositionToString pts ) {
	String toReturn = "(";
	// first position is not preceded by a comma
	if( it.hasNext() ) toReturn += " " + pts.stringfor( it.nextPosition() );
	while( it.hasNext() ) toReturn += ", " + pts.stringfor( it.nextPosition() );
	toReturn += " )";
	it.reset();
	return toReturn;
    }

    public static String stringfor( PositionIterator it ) {
	return stringfor( it, pos_to_element_s );
    }

    public static String stringfor( LocatorIterator it, LocatorToString lts ) {
	String toReturn = "(";
	// first locator is not preceded by a comma
	if( it.hasNext() ) toReturn += " " + lts.stringfor( it.nextLocator() );
	while( it.hasNext() ) toReturn += ", " + lts.stringfor( it.nextLocator() );
	toReturn += " )";
	it.reset();
	return toReturn;
    }

    public static String stringfor( LocatorIterator it ) {
	return stringfor( it, loc_to_collections_style_s );
    }
    */


    



    /** 
     * @param pos Position for which string representation is desired
     * @return verbose string representation of <code>pos</code>
     */
     public static String stringfor( Position pos ) {
	if( pos==null ) return "null position";
	else return "Position with element " + pos.element();
    }

    /** 
     * @param loc Locator for which string representation is desired
     * @return verbose string representation of <code>loc</code>
     */
     public static String stringfor( Locator loc ) {
	if( loc==null ) return "null locator";
	else return "Locator with key " + loc.key() + " = " + loc.element();
    }




    
    /** 
     * Stringifies a position by giving the string representation of the position's
     * element.
     */
     public static class PositionWritesElementOnly implements PositionToString {
	public String stringfor( Position p ) { return "" + p.element(); }
    }

    /** 
     * Stringifies a locator in the Java Collections style: (key)=(element).
     */
     public static class LocatorCollectionsStyle implements LocatorToString {
	public String stringfor( Locator loc ) {
	    return "" + loc.key() + "=" + loc.element();
	}
    }

}

