package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.awt.Font;

import org.apache.commons.collections15.Transformer;

public class VertexFontTransformer<V, E> implements Transformer<Object, Font>{
	
	private boolean show_;
	
	public void setShowFont(boolean show){
		show_ = show;
	}
	
	
	public Font transform(Object o){
		if(show_){
			System.out.println(o.toString());
			if(o instanceof VertexInfo){
				return new Font("Arial", Font.BOLD, 16);
			}
		} 
		return null;		
	}
}
