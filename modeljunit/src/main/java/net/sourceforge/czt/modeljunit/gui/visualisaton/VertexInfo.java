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


/**
 * 
 * @author Jerramy Winchester
 *
 */
public class VertexInfo {
	
	//Class wide variables
	private Object name_;
	private Boolean displayed_;
	private Boolean visited_;
	private Boolean isPicked_;
	private int incomingEdges_;
	private int outgoingEdges_;
	private Boolean isStartState_;
	private Boolean isFailedVertex_;
	
	public VertexInfo(Object name){
		name_ = name;
		displayed_ = false;
		visited_ = false;
		incomingEdges_ = 0;
		outgoingEdges_ = 0;
		setStartState(false);
		setIsFailedVertex(false);
	}	

	public VertexInfo(Object name, Boolean displayed, Boolean visited){
		name_ = name;
		displayed_ = displayed;
		visited_ = visited;
		incomingEdges_ = 0;
		outgoingEdges_ = 0;
		setStartState(false);
		setIsFailedVertex(false);
	}	

	public boolean isPicked(){		
		return isPicked_;
	}
	
	public void setIsPicked(boolean isPicked){
		isPicked_ = isPicked;
	}
	
	public String getName(){
		return name_.toString();
	}
	
	public Object getVertex(){
		return name_;
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
	
	public int getIncomingEdges() {
		return incomingEdges_;
	}

	public void setIncomingEdges(int incomingEdges_) {
		this.incomingEdges_ = incomingEdges_;
	}
	
	public int getOutgoingEdges() {
		return outgoingEdges_;
	}

	public void setOutgoingEdges(int outgoingEdges_) {
		this.outgoingEdges_ = outgoingEdges_;
	}

	/**
	 * @param isStartState_ the isStartState_ to set
	 */
	public void setStartState(boolean isStartState) {
		this.isStartState_ = isStartState;
	}

	/**
	 * @return the isStartState_
	 */
	public boolean isStartState() {
		return isStartState_;
	}

	/**
	 * @param isFailedVertex_ the isFailedVertex_ to set
	 */
	public void setIsFailedVertex(Boolean isFailedVertex) {
		this.isFailedVertex_ = isFailedVertex;
	}

	/**
	 * @return the isFailedVertex_
	 */
	public Boolean getIsFailedVertex() {
		return isFailedVertex_;
	}
}
