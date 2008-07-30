/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.GradientPaint;
import java.awt.Paint;
import java.awt.Rectangle;
import java.awt.Shape;
import java.awt.Stroke;
import java.awt.geom.AffineTransform;
import java.awt.geom.Point2D;

import javax.swing.JComponent;

import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.algorithms.util.Context;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.Layer;
import edu.uci.ics.jung.visualization.RenderContext;
import edu.uci.ics.jung.visualization.picking.PickedState;
import edu.uci.ics.jung.visualization.renderers.Renderer;
import edu.uci.ics.jung.visualization.transform.shape.GraphicsDecorator;

/**
 * @author Jerramy Winchester
 *
 */
public class VertexGradientRenderer<V,E> implements Renderer.Vertex<V,E> {

	private Color backFillColor;
	private Color dispColor;	
	private Color pickedColor;	
	private Color visColor;	
	private Color graphColor;	
	private Color stanColor;

	private PickedState<V> pickedState;
	private boolean cyclic;

	public VertexGradientRenderer(Color backFillColor, PickedState<V> pickedState, boolean cyclic) {
		this.backFillColor = backFillColor;
		this.dispColor = Color.blue;
		this.pickedColor = Color.red;		
		this.graphColor = Color.magenta;
		this.visColor = Color.green;
		this.stanColor = Color.gray;
		this.pickedState = pickedState;
		this.cyclic = cyclic;
	}


	public void paintVertex(RenderContext<V,E> rc, Layout<V,E> layout, V v) {
		Graph<V,E> graph = layout.getGraph();
		if (rc.getVertexIncludePredicate().evaluate(Context.<Graph<V,E>,V>getInstance(graph,v))) {
			boolean vertexHit = true;
			// get the shape to be rendered
			Shape shape = rc.getVertexShapeTransformer().transform(v);

			Point2D p = layout.transform(v);
			p = rc.getMultiLayerTransformer().transform(Layer.LAYOUT, p);

			float x = (float)p.getX();
			float y = (float)p.getY();

			// create a transform that translates to the location of
			// the vertex to be rendered
			AffineTransform xform = AffineTransform.getTranslateInstance(x,y);
			// transform the vertex shape with xtransform
			shape = xform.createTransformedShape(shape);

			vertexHit = vertexHit(rc, shape);			

			if (vertexHit) {
				paintShapeForVertex(rc, v, shape);
			}
		}
	}

	protected boolean vertexHit(RenderContext<V,E> rc, Shape s) {
		JComponent vv = rc.getScreenDevice();
		Rectangle deviceRectangle = null;
		if(vv != null) {
			Dimension d = vv.getSize();
			deviceRectangle = new Rectangle(
					0,0,
					d.width,d.height);
		}
		return rc.getMultiLayerTransformer().getTransformer(Layer.VIEW).transform(s).intersects(deviceRectangle);
	}

	protected void paintShapeForVertex(RenderContext<V,E> rc, V v, Shape shape) {
		GraphicsDecorator g = rc.getGraphicsContext();
		Paint oldPaint = g.getPaint();
		Rectangle r = shape.getBounds();
		float y2 = (float)r.getMaxY();
		if(cyclic) {
			y2 = (float)(r.getMinY()+r.getHeight()/2);
		}

		Paint fillPaint = null;
		if(pickedState != null && pickedState.isPicked(v)) {
			fillPaint = new GradientPaint((float)r.getMinX(), (float)r.getMinY(), backFillColor,
					(float)r.getMinX(), y2, pickedColor, cyclic);
		} else if(v instanceof Graph){
			fillPaint = new GradientPaint((float)r.getMinX(), (float)r.getMinY(), backFillColor,
					(float)r.getMinX(), y2, graphColor, cyclic);
		} else if(v instanceof VertexInfo){
			VertexInfo vert = (VertexInfo)v;
			if(vert.getIsDisplayed()){
				fillPaint = new GradientPaint((float)r.getMinX(), (float)r.getMinY(), backFillColor,
						(float)r.getMinX(), y2, dispColor, cyclic);
			} else if(vert.getIsVisited()){
				fillPaint = new GradientPaint((float)r.getMinX(), (float)r.getMinY(), backFillColor,
						(float)r.getMinX(), y2, visColor, cyclic);
			} 
			else {
				fillPaint = new GradientPaint((float)r.getMinX(), (float)r.getMinY(), backFillColor,
						(float)r.getMinX(), y2, stanColor, cyclic);
			}
		}
		if(fillPaint != null) {
			g.setPaint(fillPaint);
			g.fill(shape);
			g.setPaint(oldPaint);
		}
		Paint drawPaint = rc.getVertexDrawPaintTransformer().transform(v);
		if(drawPaint != null) {
			g.setPaint(drawPaint);
		}
		Stroke oldStroke = g.getStroke();
		Stroke stroke = rc.getVertexStrokeTransformer().transform(v);
		if(stroke != null) {
			g.setStroke(stroke);
		}
		g.draw(shape);
		g.setPaint(oldPaint);
		g.setStroke(oldStroke);
	}
}
