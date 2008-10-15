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

import java.util.TreeMap;

import net.sourceforge.czt.modeljunit.Transition;

/**
 * @author Jerramy Winchester
 *
 */
public class EdgeInfo {
	
	//Class wide variables
	private Transition transition_;
	private VertexInfo srcVertex_;
	private VertexInfo destVertex_;
	private Boolean displayed_;
	private Boolean visited_;
	private TreeMap<String, Integer> sequences_;
	private Boolean failedEdge_;
	private String failedMsg_;

	public EdgeInfo(Transition trans, VertexInfo src, VertexInfo dest){
		transition_ = trans;
		srcVertex_ = src;
		destVertex_ = dest;
		displayed_ = false;
		visited_ = false;
		failedEdge_ = false;
		failedMsg_ = new String();
		sequences_ = new TreeMap<String, Integer>();
	}
	
	public EdgeInfo(Transition trans, VertexInfo src, VertexInfo dest, Boolean displayed, Boolean visited){
		transition_ = trans;
		srcVertex_ = src;
		destVertex_ = dest;
		displayed_ = displayed;
		visited_ = visited;
		failedEdge_ = false;
		failedMsg_ = new String();
		sequences_ = new TreeMap<String, Integer>();
	}
	
	public String getAction(){		
		return transition_.getAction();
	}
	
	public Transition getTransition(){
		return transition_;
	}
	
	public Object getSrcVertexName(){
		return transition_.getStartState();
	}
	
	public VertexInfo getSrcVertex(){
		return srcVertex_;
	}
	
	public Object getDestVertexName(){
		return transition_.getEndState();
	}
	
	public VertexInfo getDestVertex(){
		return destVertex_;
	}
	
	public void setIsDisplayed(boolean displayed){
		displayed_ = displayed;
	}
	
	public Boolean getIsDisplayed(){
		return displayed_;
	}
	
	public void setIsVisited(Boolean visited){
		visited_ = visited;
	}
	
	public Boolean getIsVisited(){
		return visited_;
	}
	
	public TreeMap<String, Integer> getSequences_() {
		return sequences_;
	}

	public void addTestSequence(String sequence) {
		this.sequences_ .put(sequence,
				this.sequences_.containsKey(sequence) 
				? ((sequences_.get(sequence)) + 1) : 1);
	}	

	/**
	 * @param failedEdge_ the failedEdge_ to set
	 */
	public void setFailedEdge(Boolean failedEdge) {
		this.failedEdge_ = failedEdge;
	}

	/**
	 * @return the failedEdge_
	 */
	public Boolean getFailedEdge() {
		return failedEdge_;
	}

	/**
	 * @param failedMsg_ the failedMsg_ to set
	 */
	public void setFailedMsg(String failedMsg) {
		this.failedMsg_ = failedMsg;
	}

	/**
	 * @return the failedMsg_
	 */
	public String getFailedMsg() {
		return failedMsg_;
	}
}
