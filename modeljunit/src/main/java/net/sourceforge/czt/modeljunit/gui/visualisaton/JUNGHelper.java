/**
 Copyright (C) 2008 Jerramy Winchester
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License as published
 by the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;

import javax.swing.tree.DefaultMutableTreeNode;

import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.Transition;
import edu.uci.ics.jung.algorithms.layout.CircleLayout;
import edu.uci.ics.jung.algorithms.layout.FRLayout2;
import edu.uci.ics.jung.algorithms.layout.ISOMLayout;
import edu.uci.ics.jung.algorithms.layout.KKLayout;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.algorithms.layout.SpringLayout;
import edu.uci.ics.jung.algorithms.layout.SpringLayout.LengthFunction;
import edu.uci.ics.jung.graph.DirectedSparseMultigraph;

/**
 * @author Jerramy Winchester
 *
 */
public class JUNGHelper {

	//Class wide variables
	private static final long serialVersionUID = -14335330588100620L;

	private static JUNGHelper jView_;

	public enum LayoutType {
		CIRCLE,
		FR,		
		SPRING,
		KK,
		ISOM
	}	
	public static final LengthFunction<Object> UNITLENGTHFUNCTION = 
		new SpringLayout.UnitLengthFunction<Object>(200);

	private DirectedSparseMultigraph<Object, Object> g;	

	private HashMap<Object, Object> vertices;
	private HashMap<Transition, Object> edges;

	private DefaultMutableTreeNode top_;
	private DefaultMutableTreeNode stateChange_ = null;
	
	private boolean seenFirstState = false;

	/**
	 * Main Constructor to initialise class wide variables.
	 */
	public JUNGHelper(){
		g = new DirectedSparseMultigraph<Object, Object>();		
		top_ = new DefaultMutableTreeNode("All test sequences");
		vertices = new HashMap<Object, Object>();
		edges = new HashMap<Transition, Object>();		
	}

	/**
	 * Get an instance of this class.
	 * @return A JUNGView instance.
	 */
	public static JUNGHelper getJUNGViewInstance(){
		if(null == jView_){
			jView_ = new JUNGHelper();
		}
		return jView_;
	}

	/**
	 * Get the JUNG graph.
	 * @return The graph
	 */
	public DirectedSparseMultigraph<Object, Object> getGraph(){
		return g;
	}

	/**
	 * This will set the edge transition display value. This was implemented
	 * because the JUNG graph has limited ability to find edges efficiently.
	 * @param tr The transition we are looking for
	 * @param displayed whether or not it is displayed.
	 */
	public void setEdgeDisplayed(Transition tr, boolean displayed){
		if(edges.containsKey(tr)){
			if(edges.get(tr) instanceof EdgeInfo){
				EdgeInfo e = (EdgeInfo)edges.get(tr);
				e.setIsDisplayed(displayed);
				e.getSrcVertex().setIsDisplayed(displayed);
				e.getDestVertex().setIsDisplayed(displayed);
			}			
		}
	}

	/**
	 * This method will return an EdgeInfo object given a transition.
	 * @param tr The transition
	 * @return The EdgeInfo Object if it is found otherwise null.
	 */
	public EdgeInfo getEdge(Transition tr){
		if(edges.containsKey(tr)){
			if(edges.get(tr) instanceof EdgeInfo){
				return (EdgeInfo)edges.get(tr);
			}
		}
		return null;
	}

	/**
	 * This method will return the layout required for a visualisation viewer.
	 * @param type The type of layout required.
	 * @return The desired layout.
	 */
	public Layout<Object, Object> getLayout(LayoutType type){
		if(g.getVertexCount() > 0){
			switch(type){
			case CIRCLE: return new CircleLayout<Object, Object>(g);
			case FR: return new FRLayout2<Object, Object>(g);
			case SPRING: return new SpringLayout<Object, Object>(g, UNITLENGTHFUNCTION);
			case KK: return new KKLayout<Object, Object>(g);
			case ISOM: return new ISOMLayout<Object,Object>(g);
			default: return new FRLayout2<Object, Object>(g);
			}
		} else {			
			return new FRLayout2<Object, Object>(g);
		}
	}

	/**
	 * This is used to fully explore a graph.
	 * @param graph The GraphListener which contains the explored graph.
	 */
	public void preExploredGraph(GraphListener graph) {
		EdgeIterator graphEdges = graph.getGraph().edges();
		VertexInfo src;		
		VertexInfo dest;
		seenFirstState = false;
		while (graphEdges.hasNext()) {
			Edge e = graphEdges.nextEdge();
			if(!vertices.containsKey(graph.getGraph().origin(e).element())){
				src = new VertexInfo(graph.getGraph().origin(e).element());
			} else {
				src = (VertexInfo)vertices.get(graph.getGraph().origin(e).element());
			}
			g.addVertex(src);
			if(!seenFirstState){
				src.setStartState(true);
				seenFirstState = true;
			}
			vertices.put(src.getName(), src);

			if(!vertices.containsKey(graph.getGraph().destination(e).element())){
				dest = new VertexInfo(graph.getGraph().destination(e).element());
			} else {
				dest = (VertexInfo)vertices.get(graph.getGraph().destination(e).element());
			}
			g.addVertex(dest);
			vertices.put(dest.getName(), dest);

			Transition action = new Transition(src.getName(),(String)e.element(), dest.getName());
			EdgeInfo edge = new EdgeInfo(action, src, dest);			
			g.addEdge(edge, src, dest);
			edges.put(action, edge);

			edge.getSrcVertex().setOutgoingEdges(edge.getSrcVertex().getOutgoingEdges() + 1);
			edge.getDestVertex().setIncomingEdges(edge.getDestVertex().getIncomingEdges() + 1);

		}		
	}

	/**
	 * Reset JUNGView.
	 * when a new graph is selected.
	 */
	public void resetRunTimeInformation() {
		Collection<Object> it = g.getVertices();		
		ArrayList<Object> vert = new ArrayList<Object>();
		for(Object v: it){
			vert.add(v);
		}
		//remove all the vertices. This will remove all edges by default as well.
		for(Object vx: vert){
			g.removeVertex(vx);
		}
		//clear the tree
		top_ = new DefaultMutableTreeNode("All test sequences");		
		stateChange_ = null;
		//Clear the explored information
		vertices.clear();
		edges.clear();		
	}

	/**
	 * This will return a root tree node.
	 * @return The root node of a JTree
	 */
	public DefaultMutableTreeNode getRootTreeNode(){
		return top_;
	}

	/**
	 * This method will get all the vertices as an arraylist.
	 * @return The arraylist of vertecies.
	 */
	public ArrayList<Object> getVertices(){		
		ArrayList<Object> v = new ArrayList<Object>();
		Collection<Object> it = vertices.values();
		v.addAll(it);
		return v;
	}

	/**
	 * This is run when the graph is reset.
	 * @param str
	 */
	public void graphDoneReset(String str) {		
		stateChange_ = new DefaultMutableTreeNode(str,true);
		top_.add(stateChange_);		
	}

	/**
	 * This method lets this panel know about vertexs that have been visited by
	 * the exploration algorythm.
	 * @param vertex The name of the vertex
	 */
	public void visitedVertex(Object vertex, boolean failed) {		
		if(!vertices.containsKey(vertex)){
			VertexInfo vert = new VertexInfo(vertex, true, true);
			vert.setIsFailedVertex(failed);
			if(vertices.size() == 0){
				vert.setStartState(true);
			}
			g.addVertex(vert);
			g.removeVertex("Empty_Fail");
			vertices.put(vertex, vert);			
		}else{
			if(vertices.get(vertex) instanceof VertexInfo){
				VertexInfo v = (VertexInfo)vertices.get(vertex);			
				v.setIsDisplayed(true);
				v.setIsVisited(true);
				v.setIsFailedVertex(failed);				
			}
		}
	}

	/**
	 * This lets the visualisation panel know about any edges that have been
	 * visited and marks them as visited.
	 * @param failed 
	 * @param action
	 * @param startState
	 * @param endState
	 */
	public void visitedEdge(Transition trans, boolean failed, String failedMsg) {		
		if(!edges.containsKey(trans)){
			visitedVertex(trans.getStartState(), failed);
			visitedVertex(trans.getEndState(), failed);			
			EdgeInfo edge = new EdgeInfo(trans
					, (VertexInfo)vertices.get(trans.getStartState())
					, (VertexInfo)vertices.get(trans.getEndState())
					, true
					, true);
			edge.setFailedEdge(failed);
			edge.setFailedMsg(failedMsg);
			edge.getSrcVertex().setOutgoingEdges(edge.getSrcVertex().getOutgoingEdges() + 1);
			edge.getDestVertex().setIncomingEdges(edge.getDestVertex().getIncomingEdges() + 1);			
			g.addEdge(edge, vertices.get(trans.getStartState()), vertices.get(trans.getEndState()));
			edges.put(trans, edge);			
		}else{
			if(edges.get(trans) instanceof EdgeInfo){
				EdgeInfo edge = (EdgeInfo)edges.get(trans);
				edge.setIsDisplayed(true);
				edge.setIsVisited(true);
				edge.setFailedEdge(failed);
				edge.setFailedMsg(failedMsg);
			}
		}
		//Update the tree with the edge transition
		if(null == stateChange_){
			stateChange_ = new DefaultMutableTreeNode("Test sequence 1");
			top_.add(stateChange_);
		}
		if(edges.get(trans) instanceof EdgeInfo){
			EdgeInfo edg = (EdgeInfo)edges.get(trans);
			edg.addTestSequence(stateChange_.toString());
		}
		DefaultMutableTreeNode transition = new DefaultMutableTreeNode(trans);		
		stateChange_.add(transition);		
	}	
}
