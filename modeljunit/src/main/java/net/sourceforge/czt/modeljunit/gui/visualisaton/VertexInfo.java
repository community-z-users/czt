/**
 * 
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
	
	public VertexInfo(Object name){
		name_ = name;
		displayed_ = false;
		visited_ = false;
		incomingEdges_ = 0;
		outgoingEdges_ = 0;
	}	

	public VertexInfo(Object name, Boolean displayed, Boolean visited){
		name_ = name;
		displayed_ = displayed;
		visited_ = visited;
		incomingEdges_ = 0;
		outgoingEdges_ = 0;
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
}
