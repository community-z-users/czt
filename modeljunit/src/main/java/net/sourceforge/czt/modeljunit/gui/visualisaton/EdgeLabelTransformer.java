package net.sourceforge.czt.modeljunit.gui.visualisaton;

import org.apache.commons.collections15.Transformer;

import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.picking.PickedInfo;

public class EdgeLabelTransformer<V, E> implements Transformer<Object, String>{
	private boolean show_ = false;
	private VisualizationViewer<Object, Object> vv_;

	public EdgeLabelTransformer(VisualizationViewer<Object, Object> vv){
		vv_ = vv;
	}
	public void showEdgeLabels(boolean show){
		show_ = show;
	}

	public String transform(Object o) {

		if(o instanceof EdgeInfo){				
			EdgeInfo e = (EdgeInfo)o;				
			PickedInfo<Object> pi = vv_.getPickedEdgeState();
			if(pi.isPicked(o) || show_){
				return e.getAction();
			} 
		}
		return "";		
	}
}
