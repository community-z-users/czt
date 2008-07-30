/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.util.HashSet;
import java.util.Set;

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
	private Set<String> sequences_;	

	public EdgeInfo(Transition trans, VertexInfo src, VertexInfo dest){
		transition_ = trans;
		srcVertex_ = src;
		destVertex_ = dest;
		displayed_ = false;
		visited_ = false;
		sequences_ = new HashSet<String>();
	}
	
	public EdgeInfo(Transition trans, VertexInfo src, VertexInfo dest, Boolean displayed, Boolean visited){
		transition_ = trans;
		srcVertex_ = src;
		destVertex_ = dest;
		displayed_ = displayed;
		visited_ = visited;
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
	
	public Set<String> getSequences_() {
		return sequences_;
	}

	public void addTestSequence(String sequence) {
		this.sequences_ .add(sequence);
	}
}
