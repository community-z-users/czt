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

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics2D;
import java.awt.Paint;
import java.awt.Point;
import java.awt.Stroke;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.AdjustmentEvent;
import java.awt.event.AdjustmentListener;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.awt.geom.Point2D;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Set;

import javax.imageio.ImageIO;
import javax.swing.AbstractButton;
import javax.swing.BorderFactory;
import javax.swing.DefaultComboBoxModel;
import javax.swing.GroupLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollBar;
import javax.swing.JScrollPane;
import javax.swing.JSlider;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.JToggleButton;
import javax.swing.JTree;
import javax.swing.LayoutStyle;
import javax.swing.event.TreeExpansionEvent;
import javax.swing.event.TreeExpansionListener;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.filechooser.FileFilter;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.Transition;
import net.sourceforge.czt.modeljunit.gui.PanelAbstract;
import edu.uci.ics.jung.algorithms.layout.CircleLayout;
import edu.uci.ics.jung.algorithms.layout.FRLayout2;
import edu.uci.ics.jung.algorithms.layout.GraphElementAccessor;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.algorithms.layout.StaticLayout;
import edu.uci.ics.jung.algorithms.layout.util.Relaxer;
import edu.uci.ics.jung.algorithms.layout.util.VisRunner;
import edu.uci.ics.jung.algorithms.util.IterativeContext;
import edu.uci.ics.jung.graph.DirectedSparseMultigraph;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.Pair;
import edu.uci.ics.jung.visualization.GraphZoomScrollPane;
import edu.uci.ics.jung.visualization.Layer;
import edu.uci.ics.jung.visualization.VisualizationViewer;
import edu.uci.ics.jung.visualization.control.CrossoverScalingControl;
import edu.uci.ics.jung.visualization.control.PickingGraphMousePlugin;
import edu.uci.ics.jung.visualization.control.PluggableGraphMouse;
import edu.uci.ics.jung.visualization.control.ScalingGraphMousePlugin;
import edu.uci.ics.jung.visualization.control.TranslatingGraphMousePlugin;
import edu.uci.ics.jung.visualization.decorators.AbstractEdgeShapeTransformer;
import edu.uci.ics.jung.visualization.decorators.ConstantDirectionalEdgeValueTransformer;
import edu.uci.ics.jung.visualization.layout.LayoutTransition;
import edu.uci.ics.jung.visualization.picking.PickedState;
import edu.uci.ics.jung.visualization.renderers.GradientVertexRenderer;
import edu.uci.ics.jung.visualization.renderers.Renderer;
import edu.uci.ics.jung.visualization.subLayout.GraphCollapser;
import edu.uci.ics.jung.visualization.transform.MutableTransformer;
import edu.uci.ics.jung.visualization.util.Animator;

/**
 * @author Jerramy Winchester
 *
 */
public class PanelJUNGVisualisation extends PanelAbstract
implements ActionListener, MouseListener{
	/** serial version ID */
	private static final long serialVersionUID = -1433533076588100620L;

	//The main panels
	private static PanelJUNGVisualisation m_panelGraph;
	private static JUNGHelper jView_;

	//variables necessary for merging of vertices and edges
	private GraphCollapser collapser;
	private Set<Object> exclusions;

	// Transformers for the visualisation viewer
	private EdgeFontTransformer<Object, Font> e_eft;
	private EdgeLabelTransformer<Object, String> e_elt;
	private EdgePaintTransformer<Object, Paint> e_ept;
	private EdgeStrokeTransformer<Object, Stroke> e_est;
	private EdgeDisplayPredicate<Object, Object> e_edp;
	private VertexFontTransformer<Object, Font> v_vft;
	private VertexLabelTransformer<Object, String> v_vlt;
	private VertexGradientRenderer<Object, Object> v_vgr;
	private VertexStrokeTransformer<Object, Object> v_vst;
	private VertexShapeTransformer<Object> v_vsht;
	private VertexEdgePaintTransformer<Object, Object> v_vept;
	private VertexDisplayPredicate<Object, Object> v_vdp;

	// main visualisation components
	private Graph<Object, Object> g = null;
	private Layout<Object, Object> layout;
	private VisualizationViewer<Object, Object> vv = null;

	// Main containers for the various panels
	private static JSplitPane treeAndViz;
	private static JSplitPane vizAndControls;
	private static JSplitPane vizAndInfo;

	// Variables for the info panel
	private JPanel infoPanel;
	private StaticLayout<Object, Object> infoLayout;
	private JScrollPane infoScrollPane;
	private JTextArea infoTextArea;
	private DirectedSparseMultigraph<Object, Object> infoGraph;
	private VisualizationViewer<Object, Object> infovv;

	// Variables for the tree panel
	private JScrollBar explScrollBar;
	private JTree tree;

	// Variables for control panel
	private JButton mergeVerticesButton;
	private JButton expandVerticesButton;
	private JButton mergeEdgesButton;
	private JButton expandEdgesButton;
	private JButton resetButton;
	private JButton captureButton;
	private JCheckBox vertLabelCheckBox;
	private JCheckBox edgeLabelCheckBox;
	private JCheckBox showExploredCheckBox;
	private JComboBox vertLabelPosComboBox;
	private JComboBox layoutTypeComboBox;
	private JLabel vertLabelPos;
	private JPanel labelsPanel;
	private JPanel layoutTypePanel;
	private JPanel mergePanel;
	private JPanel capturePanel;
	private JButton animationButton;
    private JPanel animationPanel;
    private JSlider animationSlider;
    private JCheckBox animationCheckBox;
    private JToggleButton animationToggleButton;

	// Variables for animations
	protected Boolean showAnimation_;
	protected Thread animationThread_;
	// End of variables declaration

	/**
	 * The PanelGraphVisualisation constructor.
	 * This will initialise the panel and also the visualisation.
	 */
	public PanelJUNGVisualisation(){
		jView_ = JUNGHelper.getJUNGViewInstance();

		g = new DirectedSparseMultigraph<Object, Object>();

		layout = new FRLayout2<Object, Object>(g);

		vv = new VisualizationViewer<Object, Object>(layout);
		vv.setBackground(Color.white);

		//TODO find a fix for the merging of edges
		//Setup the ability to compress multiple edges into one
		/*final PredicatedParallelEdgeIndexFunction<Object, Object> eif =
			PredicatedParallelEdgeIndexFunction.getInstance();
		exclusions = new HashSet<Object>();
		eif.setPredicate(new Predicate<Object>() {
			public boolean evaluate(Object e) {
				return exclusions.contains(e);
			}});
		vv.getRenderContext().setParallelEdgeIndexFunction(eif);
		*/

		//A GraphCollapser to handle merging of vertices.
		collapser = new GraphCollapser(jView_.getGraph());

		// Initialise the animation switch
		showAnimation_ = false;

		// Create the custom mouse plugins to control the visualisation	with the mouse
		PluggableGraphMouse gm = new PluggableGraphMouse();
		gm.add(new TranslatingGraphMousePlugin(MouseEvent.BUTTON3_MASK));
		gm.add(new PickingGraphMousePlugin<Object, Object>());
		gm.add(new ScalingGraphMousePlugin(new CrossoverScalingControl(), 0, 1.1f, 0.9f));
		vv.setGraphMouse(gm);
		vv.addMouseListener(this);

		// translate the layout panel down and across so that it is not hard up
		// against the side of the splitPane box.
		MutableTransformer modelTransformer = vv.getRenderContext().getMultiLayerTransformer().getTransformer(Layer.LAYOUT);
		modelTransformer.translate(25, 25);

		// setup the transformers for the visualisation
		e_eft = new EdgeFontTransformer<Object, Font>();
		e_elt = new EdgeLabelTransformer<Object, String>(vv);
		e_ept = new EdgePaintTransformer<Object, Paint>(new Color(40, 40, 40),Color.black,vv);
		e_est = new EdgeStrokeTransformer<Object, Stroke>();
		e_edp = new EdgeDisplayPredicate<Object, Object>(false);
		v_vft = new VertexFontTransformer<Object, Font>();
		v_vlt = new VertexLabelTransformer<Object, String>();
		v_vgr = new VertexGradientRenderer<Object, Object>(Color.white, vv.getPickedVertexState(), true);
		v_vst = new VertexStrokeTransformer<Object, Object>(g, vv.getPickedVertexState());
		v_vsht = new VertexShapeTransformer<Object>();
		v_vept = new VertexEdgePaintTransformer<Object, Object>(vv.getPickedVertexState(), jView_.getVertices());
		v_vdp = new VertexDisplayPredicate<Object, Object>(false);

		// Apply the transformers
		vv.getRenderContext().setEdgeFontTransformer(e_eft);
		vv.getRenderContext().setEdgeLabelTransformer(e_elt);
		vv.getRenderContext().setEdgeDrawPaintTransformer(e_ept);
		vv.getRenderContext().setEdgeStrokeTransformer(e_est);
		vv.getRenderContext().setArrowDrawPaintTransformer(e_ept);
		vv.getRenderContext().setArrowFillPaintTransformer(e_ept);
		vv.getRenderContext().setEdgeIncludePredicate(e_edp);
		vv.getRenderContext().setVertexFontTransformer(v_vft);
		vv.getRenderContext().setVertexLabelTransformer(v_vlt);
		vv.getRenderContext().setVertexStrokeTransformer(v_vst);
		vv.getRenderContext().setVertexShapeTransformer(v_vsht);
		vv.getRenderContext().setVertexDrawPaintTransformer(v_vept);
		vv.getRenderer().setVertexRenderer(v_vgr);
		vv.getRenderContext().setVertexIncludePredicate(v_vdp);

		//Set the curvature in the edges
		AbstractEdgeShapeTransformer<Object, Object> aesf =
			(AbstractEdgeShapeTransformer<Object, Object>)vv.getRenderContext().getEdgeShapeTransformer();
		aesf.setControlOffsetIncrement(30);
		//Set the new size of the visualisation to allow for resizing of the panel
		vv.addComponentListener(new ComponentAdapter() {
			@Override
			public void componentResized(ComponentEvent arg0) {
				super.componentResized(arg0);
				layout.setSize(arg0.getComponent().getSize());
				vv.setSize(arg0.getComponent().getSize());
			}});

		// provide a scrollpane for the visualisation
		GraphZoomScrollPane vvPanel = new GraphZoomScrollPane(vv);

		//Setup the Splitpanes
		vizAndInfo = new JSplitPane(JSplitPane.VERTICAL_SPLIT, vvPanel, getInfoPanel());
		vizAndInfo.setResizeWeight(1.0);
		vizAndInfo.setOneTouchExpandable(true);

		vizAndControls = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, vizAndInfo, getControlPanel());
		vizAndControls.setResizeWeight(1.0);
		vizAndControls.setOneTouchExpandable(true);

		treeAndViz = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, getTreeControls(), vizAndControls);
		treeAndViz.setResizeWeight(0.0);
		treeAndViz.setOneTouchExpandable(true);

		setLayout(new BorderLayout());
		add(treeAndViz, BorderLayout.CENTER);
	}

	/**
	 * Use singleton pattern to get instance of graph view panel
	 * @return An instance of the PanelGraphVisualistation panel
	 */
	public static PanelJUNGVisualisation getGraphVisualisationInstance()
	{
		if (m_panelGraph == null){
			m_panelGraph = new PanelJUNGVisualisation();
		}
		return m_panelGraph;
	}

	/**
	 * This will show the fully explored graph
	 * @param graph The GraphListener which contains the explored graph.
	 */
	public void showEmptyExploredGraph(GraphListener graph) {
		jView_.preExploredGraph(graph);
	}

	/**
	 * This is run to reset the tree view and the panel
	 * when a new graph is selected.
	 */
	public void resetRunTimeInformation() {
		jView_.resetRunTimeInformation();
	}

	/** 
	 * This should be called by the top-level program whenever the
	 *  model changes.
	 */
	public void newModel()
	{
	  resetRunTimeInformation();
	}

	/**
	 * This method gives the controls access to the visualisation viewer.
	 * @return The visualisation viewer.
	 */
	public VisualizationViewer<Object, Object> getVisualisationViewer(){
		return vv;
	}

	/**
	 * This method is used to update the panel. This is
	 * used to start the animation off.
	 * @param showAnimation
	 */
	public void updateGUI(boolean showAnimation) {
		//System.out.println("Doing update GUI");
		// Reset the info panel
		updateInfoPanel("Nothing Selected");
		// Setup the tree
		tree.setModel(new DefaultTreeModel(jView_.getRootTreeNode()));
		// Setup the test sequence scroll bar
		explScrollBar.setMaximum(tree.getRowCount());
		explScrollBar.setMinimum(0);
		explScrollBar.setVisibleAmount(1);

		layout.setSize(new Dimension(vizAndInfo.getWidth() - 75
				, vizAndInfo.getHeight() - infoPanel.getHeight() - 75));

		vv.getModel().setGraphLayout(layout, new Dimension(vizAndInfo.getWidth() - 20
				, vizAndInfo.getHeight() - infoPanel.getHeight() - 32));

		g = new DirectedSparseMultigraph<Object, Object>();

		// Start the animation
		if(showAnimation && animationCheckBox.isSelected()){
			showAnimation_ = true;
		} else {
			showAnimation_ = false;
		}
		// Make sure the pause button is unselected
		animationToggleButton.setSelected(false);
		// Start the animation off
		animationThread_ = new AnimateThread(tree);
		animationThread_.start();

	}

	/**
	 * This will update the info panel based on what object is passed to it. The info
	 * panel is used to show information about the visualisation.
	 * @param obj The Object to show information about.
	 */
	@SuppressWarnings("unchecked")
	public void updateInfoPanel(Object obj){
		Collection<Object> it = infoGraph.getVertices();
		ArrayList<Object> vert = new ArrayList<Object>();
		// make sure that the object is not null
		if(null == obj){
			return;
		}
		for(Object v: it){
			vert.add(v);
		}
		//remove all the vertices. This will remove all edges by default as well.
		for(Object vx: vert){
			infoGraph.removeVertex(vx);
		}
		//Remove all the text from the text area.
		infoTextArea.setText("");

		if(obj instanceof VertexInfo){
			infoGraph.addVertex((VertexInfo)obj);
			infoLayout.setLocation((VertexInfo)obj, new Point(30, 50));
			infoTextArea.append("State Selected: " + ((VertexInfo)obj).getName() + "\n");
			infoTextArea.append("--------------------------------\n");
			infoTextArea.append("Transition Pairs: " + (((VertexInfo)obj).getIncomingEdges() * ((VertexInfo)obj).getOutgoingEdges()) + "\n");
		} else if(obj instanceof Graph){
			StringBuffer str = new StringBuffer();
			for(Object i: ((Graph)obj).getVertices()){
				if(i instanceof VertexInfo){
					VertexInfo v = (VertexInfo)i;
					if(str.length() % 25 > 20){
						str.append("\n");
					}
					str.append(v.getName() + ", ");
				}
			}
			if(str.length() > 1){
				str.deleteCharAt(str.length() - 1);
				str.deleteCharAt(str.length() - 1);
			}
			infoGraph.addVertex(" - Merged States");
			infoLayout.setLocation(" - Merged States", new Point(30, 50));
			infoTextArea.append("Merged states are:\n" + str.toString());
			infoTextArea.setCaretPosition(0);
		} else if(obj instanceof EdgeInfo){
			String srcVertex = "Source State: " + ((EdgeInfo)obj).getSrcVertex().getName();
			String destVertex = "Destination State: " + ((EdgeInfo)obj).getDestVertex().getName();
			String edge = "                                                  Action taken: " + ((EdgeInfo)obj).getAction();
			infoGraph.addVertex(destVertex);
			if(!((EdgeInfo)obj).getSrcVertex().getName().equals(((EdgeInfo)obj).getDestVertex().getName())){
				infoGraph.addVertex(srcVertex);
				infoLayout.setLocation(srcVertex, new Point(30, 20));
				infoLayout.setLocation(destVertex, new Point(30, 85));
				infoGraph.addEdge((EdgeInfo)obj, srcVertex, destVertex);
			} else {
				infoGraph.addEdge((EdgeInfo)obj, destVertex, destVertex);
				infoLayout.setLocation(destVertex, new Point(30, 65));
			}
			

			infoTextArea.append("Action selected: " + ((EdgeInfo)obj).getAction() + "\n");
			if(null != ((EdgeInfo)obj).getFailedMsg()){
				infoTextArea.append("Failure occured: " + ((EdgeInfo)obj).getFailedMsg() + "\n");
			}
			if(((EdgeInfo)obj).getSequences_().size() == 0){
				infoTextArea.append("--------------------------------\nnot tested:\n");
			} else {
				infoTextArea.append("--------------------------------\nused in:\n");
				Iterator<String> itr = ((EdgeInfo)obj).getSequences_().keySet().iterator();
				while(itr.hasNext()){
					String seq = itr.next();
					infoTextArea.append(seq + " (taken " + ((EdgeInfo)obj).getSequences_().get(seq) + " times)\n");
				}
			}
			infoTextArea.setCaretPosition(0);
		} else {
			infoTextArea.append(obj.toString() + "\n");
		}
		infovv.repaint();
	}

	/**
	 * The override required by implementing the ActionPerformed class.
	 */
	@SuppressWarnings("unchecked")
	@Override
	public void actionPerformed(ActionEvent e) {
		AbstractButton source = (AbstractButton)e.getSource();
		// The show vertex labels checkbox
		if (source == vertLabelCheckBox){
			v_vlt.setShowLabels(vertLabelCheckBox.isSelected());
			// The show vertex labels checkbox
		} else if (source == edgeLabelCheckBox){
			e_elt.showEdgeLabels(edgeLabelCheckBox.isSelected());
			// The show explored label checkbox
		} else if (source == showExploredCheckBox){
			v_vdp.showExplored(!showExploredCheckBox.isSelected());
			e_edp.showExplored(!showExploredCheckBox.isSelected());
			// Merge vertices button
		} else if (source == mergeVerticesButton){
			Collection<VertexInfo> picked = new HashSet(vv.getPickedVertexState().getPicked());
			if(picked.size() > 1) {
				Graph<Object, Object> inGraph = layout.getGraph();
				Graph<Object, Object> clusterGraph = collapser.getClusterGraph(inGraph, picked);
				Graph<Object, Object> graph = collapser.collapse(inGraph, clusterGraph);
				double sumx = 0;
				double sumy = 0;
				for(Object v : picked) {
					Point2D p = (Point2D)layout.transform(v);
					sumx += p.getX();
					sumy += p.getY();
				}
				//Position the new merged vertex in the center where the other vertices used to be.
				Point2D cp = new Point2D.Double(sumx/picked.size(), sumy/picked.size());
				vv.getRenderContext().getParallelEdgeIndexFunction().reset();
				layout.setGraph(graph);
				layout.setLocation(clusterGraph, cp);
				g = graph;
				animateLayoutChanges();
			}

			// Expand vertices button
		} else if (source == expandVerticesButton){
			Collection<VertexInfo> picked = new HashSet(vv.getPickedVertexState().getPicked());
			for(Object v : picked) {
				if(v instanceof Graph) {
					Graph<Object, Object> graph = collapser.expand(layout.getGraph(), (Graph<VertexInfo, EdgeInfo>)v);
					vv.getRenderContext().getParallelEdgeIndexFunction().reset();
					layout.setGraph(graph);
					g = graph;
					animateLayoutChanges();
				}
			}

			// Merge Edges button
		} else if (source == mergeEdgesButton){
			Collection<Object> picked = vv.getPickedVertexState().getPicked();
			if(picked.size() == 2) {
				Pair<Object> pair = new Pair<Object>(picked);
				Graph<Object, Object> graph = layout.getGraph();
				Collection<Object> edges = new HashSet<Object>(graph.getIncidentEdges(pair.getFirst()));
				edges.retainAll(graph.getIncidentEdges(pair.getSecond()));
				exclusions.addAll(edges);
				for(Object o: exclusions){
					EdgeInfo edge = (EdgeInfo)o;
					System.out.println("edge:"+edge.getAction());
				}
			}
			if(picked.size() == 1){
				Graph<Object, Object> graph = layout.getGraph();
				for(Object o: picked){
					if(o instanceof VertexInfo){
						VertexInfo v = (VertexInfo)o;
						Collection<Object> ed = graph.getInEdges(v);
						for(Object oe: ed){
							if(oe instanceof EdgeInfo){
								EdgeInfo edg = (EdgeInfo)oe;
								if(edg.getDestVertex().equals(edg.getSrcVertex())){
									exclusions.add(edg);
								}
							}
						}
					}
				}
				for(Object o: exclusions){
					EdgeInfo edge = (EdgeInfo)o;
					System.out.println("edge:"+edge.getAction());
				}
			}
			// Expand edges button
		} else if (source == expandEdgesButton){
			Collection<Object> picked = vv.getPickedVertexState().getPicked();
			if(picked.size() == 2) {
				Pair<Object> pair = new Pair<Object>(picked);
				Graph<Object, Object> graph = layout.getGraph();
				Collection<Object> edges = new HashSet<Object>(graph.getIncidentEdges(pair.getFirst()));
				edges.retainAll(graph.getIncidentEdges(pair.getSecond()));
				exclusions.removeAll(edges);
			}else if(picked.size() == 1){
				Graph<Object, Object> graph = layout.getGraph();
				for(Object o: picked){
					if(o instanceof VertexInfo){
						VertexInfo v = (VertexInfo)o;
						Collection<Object> ed = graph.getInEdges(v);
						for(Object oe: ed){
							if(oe instanceof EdgeInfo){
								EdgeInfo edg = (EdgeInfo)oe;
								if(edg.getDestVertex().equals(edg.getSrcVertex())){
									exclusions.remove(edg);
								}
							}
						}
					}
				}
			}

			// The reset button
		} else if (source == resetButton){
			Collection<Object> vertices = layout.getGraph().getVertices();
			for(Object v : vertices) {
				if(v instanceof Graph) {
					Graph<Object, Object> graph = collapser.expand(layout.getGraph(), (Graph<VertexInfo, EdgeInfo>)v);
					vv.getRenderContext().getParallelEdgeIndexFunction().reset();
					layout.setGraph(graph);
					g = graph;
					animateLayoutChanges();
				}
			}
			//exclusions.clear();

			// The capture button
		} else if (source == captureButton){
			JFileChooser chooser = new JFileChooser();
			chooser.setCurrentDirectory(new File("."));
			chooser.addChoosableFileFilter(new FileFilter() {

				@Override
				public boolean accept(File f) {
					if (f.isDirectory()) {
						return true;
					}
					if (f.getName().endsWith(".png")) {
						return true;
					} else {
						return false;
					}
				}

				@Override
				public String getDescription() {
					return "*.png";
				}

			});
			int returnVal = chooser.showSaveDialog(null);

			if (returnVal == JFileChooser.APPROVE_OPTION) {
				File file = chooser.getSelectedFile();
				if (!file.getName().toLowerCase().endsWith(".png")) {
					// Add .png extension
					file = new File(file.getAbsolutePath() + ".png");
				}
				System.out.println("Saving screenshot to file " + file);

				int width = vv.getWidth();
				int height = vv.getHeight();
				BufferedImage image = new BufferedImage(width, height,
						BufferedImage.TYPE_INT_RGB);
				Graphics2D g2 = image.createGraphics();
				vv.paint(g2);
				g2.dispose();
				try {
					ImageIO.write(image, "png", file);
				} catch (IOException ioe) {
					System.out.println(ioe.getMessage());
				}
			} else {
				System.out.println("User pressed cancel, or something went wrong");
			}
			// The animation button  used to stop the animation
		}  else if (source == animationButton){
			showAnimation_ = false;
			// The pause animation toggle button
		}  else if (source == animationToggleButton){
			if(!animationToggleButton.isSelected()){
				try{
					animationThread_.interrupt();
				} catch (Exception ex){
				//Ignore
				}
			}

		}
		vv.repaint();
	}

	@Override
	public void mouseClicked(MouseEvent e) {
	}

	@Override
	public void mouseEntered(MouseEvent e) {
	}

	@Override
	public void mouseExited(MouseEvent e) {
	}

	/**
	 * This is used to listen to click events within
	 * the visualisation viewer.
	 */
	@Override
	public void mousePressed(MouseEvent e) {
		GraphElementAccessor<Object, Object> pickSupport = vv.getPickSupport();
		PickedState<Object> pickedVertexState = vv.getPickedVertexState();
		PickedState<Object> pickedEdgeState = vv.getPickedEdgeState();
		if(pickSupport != null && e.getButton() == MouseEvent.BUTTON1) {
			Layout<Object, Object> layout = vv.getGraphLayout();
			// p is the screen point for the mouse event
			Point2D p = e.getPoint();
			if(pickSupport.getVertex(layout, p.getX(), p.getY()) != null){
				Object vertex = pickSupport.getVertex(layout, p.getX(), p.getY());
				pickedEdgeState.clear();
				updateInfoPanel(vertex);
			}else if(pickSupport.getEdge(layout, p.getX(), p.getY()) != null){
				Object edge = pickSupport.getEdge(layout, p.getX(), p.getY());
				pickedVertexState.clear();
				updateInfoPanel(edge);

			} else {
				updateInfoPanel("Nothing Selected");
			}
			// Stop any animation that is running if the toggle button isn't
			// selected.
			showAnimation_ = animationToggleButton.isSelected();
		}
	}

	@Override
	public void mouseReleased(MouseEvent e) {
	}

	/**
	 * This creates the controls panel
	 * @return The JPanel with all the controls on it.
	 */
	private JPanel getControlPanel() {
		JPanel panel = new JPanel();
		labelsPanel = new JPanel();
		vertLabelCheckBox = new JCheckBox();
		edgeLabelCheckBox = new JCheckBox();
		showExploredCheckBox = new JCheckBox();
		vertLabelPos = new JLabel();
		vertLabelPosComboBox = new JComboBox();
		layoutTypePanel = new JPanel();
		layoutTypeComboBox = new JComboBox();
		mergePanel = new JPanel();
		mergeVerticesButton = new JButton();
		expandVerticesButton = new JButton();
		mergeEdgesButton = new JButton();
		expandEdgesButton = new JButton();
		resetButton = new JButton();
		capturePanel = new JPanel();
		captureButton = new JButton();
		animationPanel = new JPanel();
        animationSlider = new JSlider();
        animationButton = new JButton();
        animationCheckBox = new JCheckBox();
        animationToggleButton = new JToggleButton();

		labelsPanel.setBorder(BorderFactory.createTitledBorder("Labels"));

		vertLabelCheckBox.setText("Show vertex labels");
		vertLabelCheckBox.addActionListener(this);
		vertLabelCheckBox.setSelected(true);

		edgeLabelCheckBox.setText("Show edge labels");
		edgeLabelCheckBox.addActionListener(this);

		showExploredCheckBox.setText("Show unexplored states/actions");
		showExploredCheckBox.addActionListener(this);
		showExploredCheckBox.setSelected(true);

		vertLabelPos.setText("Label position:");

		vertLabelPosComboBox.setModel(new DefaultComboBoxModel(
				new Renderer.VertexLabel.Position[] {
						Renderer.VertexLabel.Position.AUTO
						, Renderer.VertexLabel.Position.CNTR
						, Renderer.VertexLabel.Position.N
						, Renderer.VertexLabel.Position.NE
						, Renderer.VertexLabel.Position.E
						, Renderer.VertexLabel.Position.SE
						, Renderer.VertexLabel.Position.S
						, Renderer.VertexLabel.Position.SW
						, Renderer.VertexLabel.Position.W
						, Renderer.VertexLabel.Position.NW}));
		vertLabelPosComboBox.addItemListener(new ItemListener() {
			public void itemStateChanged(ItemEvent e) {
				Renderer.VertexLabel.Position position =
					(Renderer.VertexLabel.Position)e.getItem();
				vv.getRenderer().getVertexLabelRenderer().setPosition(position);
				vv.repaint();
			}});
		vertLabelPosComboBox.setSelectedItem(Renderer.VertexLabel.Position.AUTO);

		GroupLayout jPanel1Layout = new GroupLayout(labelsPanel);
		labelsPanel.setLayout(jPanel1Layout);
		jPanel1Layout.setHorizontalGroup(
	            jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
	            .addGroup(jPanel1Layout.createSequentialGroup()
	                .addGroup(jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
	                    .addComponent(vertLabelCheckBox)
	                    .addGroup(jPanel1Layout.createSequentialGroup()
	                        .addComponent(vertLabelPos)
	                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
	                        .addComponent(vertLabelPosComboBox, 0, 127, Short.MAX_VALUE))
	                    .addComponent(edgeLabelCheckBox)
	                    .addComponent(showExploredCheckBox))
	                .addContainerGap())
	        );
	        jPanel1Layout.setVerticalGroup(
	            jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
	            .addGroup(jPanel1Layout.createSequentialGroup()
	                .addComponent(vertLabelCheckBox)
	                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
	                .addGroup(jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
	                    .addGroup(jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
	                        .addComponent(vertLabelPos)
	                        .addComponent(vertLabelPosComboBox, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE))
	                    .addGroup(jPanel1Layout.createSequentialGroup()
	                        .addGap(25, 25, 25)
	                        .addGroup(jPanel1Layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
	                            .addComponent(edgeLabelCheckBox))))
	                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED, 2, Short.MAX_VALUE)
	                .addComponent(showExploredCheckBox))
	        );

		layoutTypePanel.setBorder(BorderFactory.createTitledBorder("Layout Type"));

		layoutTypeComboBox.setModel(new DefaultComboBoxModel(
				new JUNGHelper.LayoutType[] { JUNGHelper.LayoutType.FR
						, JUNGHelper.LayoutType.CIRCLE
						, JUNGHelper.LayoutType.ISOM
						, JUNGHelper.LayoutType.KK
						, JUNGHelper.LayoutType.SPRING}));
		layoutTypeComboBox.addItemListener(new ItemListener() {
			public void itemStateChanged(ItemEvent e) {
				try{
					if(e.getStateChange() == ItemEvent.SELECTED){
						Layout<Object, Object> l = jView_.getLayout((JUNGHelper.LayoutType)e.getItem());
						l.setGraph(g);
						l.setInitializer(vv.getGraphLayout());
						l.setSize(vv.getSize());
						LayoutTransition<Object, Object> lt =
							new LayoutTransition<Object, Object>(vv, vv.getGraphLayout(), l);
						Animator animator = new Animator(lt);
						animator.start();

						layout = l;
						vv.repaint();
					}
				} catch (Exception ex){
					ex.printStackTrace();
				}

			}});
		layoutTypeComboBox.setSelectedItem(JUNGHelper.LayoutType.FR);

		GroupLayout layoutTypePanelLayout = new GroupLayout(layoutTypePanel);
		layoutTypePanel.setLayout(layoutTypePanelLayout);
		layoutTypePanelLayout.setHorizontalGroup(
				layoutTypePanelLayout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addComponent(layoutTypeComboBox, 0, 178, Short.MAX_VALUE)
		);
		layoutTypePanelLayout.setVerticalGroup(
				layoutTypePanelLayout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(layoutTypePanelLayout.createSequentialGroup()
						.addComponent(layoutTypeComboBox, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
						.addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
		);

		mergePanel.setBorder(BorderFactory.createTitledBorder("Merge"));

		mergeVerticesButton.setText("Merge states");
		mergeVerticesButton.addActionListener(this);

		expandVerticesButton.setText("Expand states");
		expandVerticesButton.addActionListener(this);

		mergeEdgesButton.setText("Merge transitions");
		mergeEdgesButton.addActionListener(this);

		expandEdgesButton.setText("Expand transitions");
		expandEdgesButton.addActionListener(this);

		resetButton.setText("Reset");
		resetButton.addActionListener(this);

		GroupLayout jPanel3Layout = new GroupLayout(mergePanel);
		mergePanel.setLayout(jPanel3Layout);
		jPanel3Layout.setHorizontalGroup(
				jPanel3Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addComponent(expandVerticesButton, GroupLayout.DEFAULT_SIZE, 151, Short.MAX_VALUE)
				.addComponent(mergeVerticesButton, GroupLayout.DEFAULT_SIZE, 151, Short.MAX_VALUE)
				//TODO add these back when the merge edges has been fixed.
				//.addComponent(mergeEdgesButton, GroupLayout.DEFAULT_SIZE, 151, Short.MAX_VALUE)
				//.addComponent(expandEdgesButton, GroupLayout.DEFAULT_SIZE, 151, Short.MAX_VALUE)
				.addComponent(resetButton, GroupLayout.DEFAULT_SIZE, 151, Short.MAX_VALUE)
		);
		jPanel3Layout.setVerticalGroup(
				jPanel3Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(jPanel3Layout.createSequentialGroup()
						.addComponent(mergeVerticesButton)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(expandVerticesButton)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						// TODO add these back when the merge edges has been fixed.
						//.addComponent(mergeEdgesButton)
						//.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED, 7, Short.MAX_VALUE)
						//.addComponent(expandEdgesButton)
						//.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(resetButton)
						.addContainerGap())
		);

		animationPanel.setBorder(javax.swing.BorderFactory.createTitledBorder("Animation"));

		//Create the label table
		Hashtable<Integer, JLabel> labelTable = new Hashtable<Integer, JLabel>();
		labelTable.put( new Integer( 100 ), new JLabel("Fast") );
		labelTable.put( new Integer( 1000 ), new JLabel("Normal") );
		labelTable.put( new Integer( 3000 ), new JLabel("Slow") );
		animationSlider.setLabelTable( labelTable );
		animationSlider.setPaintLabels(true);
        animationSlider.setMajorTickSpacing(500);
        animationSlider.setMaximum(3000);
        animationSlider.setMinimum(100);
        animationSlider.setValue(1000);
        animationSlider.setPaintTicks(true);
        animationSlider.setToolTipText("Use this slider to control the speed of the animation");

        animationButton.setText("Stop ");
        animationButton.addActionListener(this);

        animationCheckBox.setText("Show animation");
        animationCheckBox.setSelected(true);

        animationToggleButton.setText("Pause");
        animationToggleButton.addActionListener(this);

        javax.swing.GroupLayout animationPanelLayout = new javax.swing.GroupLayout(animationPanel);
        animationPanel.setLayout(animationPanelLayout);
        animationPanelLayout.setHorizontalGroup(
            animationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(animationPanelLayout.createSequentialGroup()
                .addContainerGap()
                .addGroup(animationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(animationSlider, javax.swing.GroupLayout.Alignment.TRAILING, javax.swing.GroupLayout.DEFAULT_SIZE, 157, Short.MAX_VALUE)
                    .addGroup(animationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING, false)
                        .addGroup(animationPanelLayout.createSequentialGroup()
                            .addComponent(animationToggleButton, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                            .addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
                            .addComponent(animationButton, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
                        .addComponent(animationCheckBox, javax.swing.GroupLayout.Alignment.LEADING)))
                .addContainerGap())
        );
        animationPanelLayout.setVerticalGroup(
            animationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(animationPanelLayout.createSequentialGroup()                
                .addComponent(animationCheckBox)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(animationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(animationToggleButton)
                    .addComponent(animationButton))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(animationSlider, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addContainerGap(21, Short.MAX_VALUE))
        );

		capturePanel.setBorder(BorderFactory.createTitledBorder("Capture"));

		captureButton.setText("Save as image");
		captureButton.addActionListener(this);

		GroupLayout jPanel4Layout = new GroupLayout(capturePanel);
		capturePanel.setLayout(jPanel4Layout);
		jPanel4Layout.setHorizontalGroup(
				jPanel4Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addComponent(captureButton, GroupLayout.DEFAULT_SIZE, 151, Short.MAX_VALUE)
		);
		jPanel4Layout.setVerticalGroup(
				jPanel4Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(jPanel4Layout.createSequentialGroup()
						.addComponent(captureButton)
						.addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
		);

		GroupLayout layout = new GroupLayout(panel);
		panel.setLayout(layout);
		layout.setHorizontalGroup(
				layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addComponent(layoutTypePanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(labelsPanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(mergePanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(capturePanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(animationPanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
		);
		layout.setVerticalGroup(
				layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(layout.createSequentialGroup()
						.addComponent(labelsPanel, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(layoutTypePanel, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(mergePanel, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(capturePanel, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
						.addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
		                .addComponent(animationPanel, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
		                .addContainerGap(104, Short.MAX_VALUE))
		);
		return panel;
	}

	/**
	 * This method will return the tree panel for the left side of the visualisation.
	 * @return	JPanel The panel containing the tree and associated controls.
	 */
	private JPanel getTreeControls(){
		JPanel panel = new JPanel();
		JButton expandButton = new JButton();
		JButton collapseButton = new JButton();
		JScrollPane jScrollPane1 = new JScrollPane();
		JPanel jPanel2 = new JPanel();
		explScrollBar = new JScrollBar();

		// setup the expand button
		expandButton.setText("Expand All");
		expandButton.addActionListener(new ActionListener(){
			public void actionPerformed(final ActionEvent e){
				for (int i = 0; i < tree.getRowCount(); i++){
					tree.expandRow(i);
				}
			}
		});

		// setup the collapse button
		collapseButton.setText("Collapse All");
		collapseButton.addActionListener(new ActionListener(){
			public void actionPerformed(final ActionEvent e){
				for (int i = 1; i < tree.getRowCount(); i++){
					tree.collapseRow(i);
				}
			}
		});

		// setup the scrollbar so the user can quickly scroll through the test sequences
		explScrollBar.setOrientation(JScrollBar.HORIZONTAL);
		explScrollBar.setToolTipText("Use the slider to scroll through test sequences");
		explScrollBar.addAdjustmentListener(new AdjustmentListener() {
			public void adjustmentValueChanged(AdjustmentEvent evt) {
				explScrollBar.setMaximum(tree.getRowCount());
				explScrollBar.setMinimum(0);
				explScrollBar.setVisibleAmount(1);
				tree.setSelectionPath(tree.getPathForRow(explScrollBar.getValue()));
				tree.scrollPathToVisible(tree.getSelectionPath());
			}
		});

		// setup the tree
		tree = new JTree(jView_.getRootTreeNode());
		tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
		tree.addTreeSelectionListener(new TreeSelectionListener(){
			@SuppressWarnings("unchecked")
			public void valueChanged(TreeSelectionEvent e) {
				//if(!showAnimation_){
					explScrollBar.setMaximum(tree.getRowCount());
					explScrollBar.setValue(tree.getMinSelectionRow());
				//}
				DefaultMutableTreeNode node = (DefaultMutableTreeNode)
				tree.getLastSelectedPathComponent();
				PickedState<Object> pickedVertexState = vv.getPickedVertexState();
				PickedState<Object> pickedEdgeState = vv.getPickedEdgeState();
				if (node == null) return;

				if (node.isLeaf() && !node.isRoot()) {
					Collection<Object> checkEdges = g.getEdges();
					for(Object ed: checkEdges){
						if(ed instanceof EdgeInfo){
							EdgeInfo ei = (EdgeInfo)ed;
							ei.setIsDisplayed(false);
							ei.getSrcVertex().setIsDisplayed(false);
							ei.getDestVertex().setIsDisplayed(false);
						}
					}
					DefaultMutableTreeNode tempNode = null;
					Enumeration enumt = node.getParent().children();

					while(enumt.hasMoreElements()){
						tempNode = (DefaultMutableTreeNode)enumt.nextElement();
						if(tempNode.getUserObject() instanceof Transition
								&& node.getParent().getIndex(tempNode)<= node.getParent().getIndex(node)){
							Transition nodeInfo = (Transition)tempNode.getUserObject();
							jView_.setEdgeDisplayed(nodeInfo, true);
							pickedEdgeState.clear();
							pickedVertexState.clear();
							pickedEdgeState.pick(jView_.getEdge(nodeInfo), true);
							pickedVertexState.pick(jView_.getEdge(nodeInfo).getDestVertex(), true);
							pickedVertexState.pick(jView_.getEdge(nodeInfo).getSrcVertex(), true);
							updateInfoPanel(jView_.getEdge(nodeInfo));
						}
					}
					vv.repaint();
				} else if(node.isRoot()){
					Collection<Object> checkEdges = g.getEdges();
					for(Object ed: checkEdges){
						if(ed instanceof EdgeInfo){
							EdgeInfo ei = (EdgeInfo)ed;
							if(ei.getIsVisited()){
								ei.setIsDisplayed(true);
								ei.getSrcVertex().setIsDisplayed(true);
								ei.getDestVertex().setIsDisplayed(true);
							}
						}
					}
					pickedEdgeState.clear();
					pickedVertexState.clear();
					updateInfoPanel("Nothing Selected");
					vv.repaint();
				} else {
					Collection<Object> checkEdges = g.getEdges();
					for(Object ed: checkEdges){
						if(ed instanceof EdgeInfo){
							EdgeInfo ei = (EdgeInfo)ed;
							ei.setIsDisplayed(false);
							ei.getSrcVertex().setIsDisplayed(false);
							ei.getDestVertex().setIsDisplayed(false);
						}
					}
					DefaultMutableTreeNode tempNode = null;
					Enumeration enumt = node.children();
					while(enumt.hasMoreElements()){
						tempNode = (DefaultMutableTreeNode)enumt.nextElement();
						if(tempNode.getUserObject() instanceof Transition){
							Transition nodeInfo = (Transition)tempNode.getUserObject();
							jView_.setEdgeDisplayed(nodeInfo, true);
						}
					}
					pickedEdgeState.clear();
					pickedVertexState.clear();
					updateInfoPanel("Nothing Selected");
					vv.repaint();
				}
			}
		});

		tree.addTreeExpansionListener(new TreeExpansionListener(){

			@Override
			public void treeCollapsed(TreeExpansionEvent arg0) {
				explScrollBar.setMaximum(tree.getRowCount());
				explScrollBar.setMinimum(0);
				explScrollBar.setValue(tree.getMinSelectionRow());
			}

			@Override
			public void treeExpanded(TreeExpansionEvent arg0) {
				explScrollBar.setMaximum(tree.getRowCount());
				explScrollBar.setMinimum(0);
				explScrollBar.setValue(tree.getMinSelectionRow());
			}
		});
		// add the tree into a scrollpane.
		jScrollPane1.setViewportView(tree);

		jPanel2.setBorder(BorderFactory.createTitledBorder("Test Sequences"));

		GroupLayout jPanel2Layout = new GroupLayout(jPanel2);
		jPanel2.setLayout(jPanel2Layout);
		jPanel2Layout.setHorizontalGroup(
				jPanel2Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(jPanel2Layout.createSequentialGroup()
						.addContainerGap()
						.addComponent(explScrollBar, GroupLayout.DEFAULT_SIZE, 166, Short.MAX_VALUE)
						.addContainerGap())
		);
		jPanel2Layout.setVerticalGroup(
				jPanel2Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(jPanel2Layout.createSequentialGroup()
						.addComponent(explScrollBar, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
						.addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
		);

		GroupLayout layout = new GroupLayout(panel);
		panel.setLayout(layout);
		layout.setHorizontalGroup(
				layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(GroupLayout.Alignment.TRAILING, layout.createSequentialGroup()
						.addComponent(expandButton, GroupLayout.DEFAULT_SIZE, 94, Short.MAX_VALUE)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(collapseButton, GroupLayout.DEFAULT_SIZE, 98, Short.MAX_VALUE))
						.addComponent(jPanel2, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
						.addComponent(jScrollPane1, GroupLayout.DEFAULT_SIZE, 198, Short.MAX_VALUE)
		);
		layout.setVerticalGroup(
				layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(layout.createSequentialGroup()
						.addGroup(layout.createParallelGroup(GroupLayout.Alignment.BASELINE)
								.addComponent(collapseButton)
								.addComponent(expandButton))
								.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
								.addComponent(jPanel2, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
								.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
								.addComponent(jScrollPane1, GroupLayout.DEFAULT_SIZE, 524, Short.MAX_VALUE))
		);

		return panel;
	}

	/**
	 * Create the Info Panel to display information about various parts of the visualisation
	 * @return The panel with the various controls on it.
	 */
	private JPanel getInfoPanel(){
		infoGraph = new DirectedSparseMultigraph<Object, Object>();

		infoLayout = new StaticLayout<Object, Object>(infoGraph);

		infovv = new VisualizationViewer<Object, Object>(infoLayout, new Dimension(200,100));
		infovv.getRenderContext().setVertexLabelTransformer(new InfoLabelTransformer<Object, Object>());
		infovv.getRenderContext().setEdgeLabelTransformer(new InfoLabelTransformer<Object, Object>());
		infovv.getRenderContext().getEdgeLabelRenderer().setRotateEdgeLabels(false);		
		infovv.getRenderContext().setEdgeDrawPaintTransformer(e_ept);		
		infovv.getRenderContext().setArrowDrawPaintTransformer(e_ept);
		infovv.getRenderContext().setArrowFillPaintTransformer(e_ept);
		infovv.getRenderContext().setEdgeLabelClosenessTransformer(new ConstantDirectionalEdgeValueTransformer<Object, Object>(.2, .2));
		infovv.getRenderer().getVertexLabelRenderer().setPosition(Renderer.VertexLabel.Position.E);
		infovv.getRenderer().setVertexRenderer(
				new GradientVertexRenderer<Object,Object>(
						Color.white, Color.green,
						Color.white, Color.green,
						vv.getPickedVertexState(),
						true));

		infoPanel = new JPanel();
		infoPanel.setMinimumSize(new Dimension(300,100));
		infoScrollPane = new javax.swing.JScrollPane();
		infoTextArea = new javax.swing.JTextArea();
		infoTextArea.setLineWrap(true);
		infoTextArea.append("Nothing Selected");

		javax.swing.GroupLayout vvPanelLayout = new javax.swing.GroupLayout(infovv);
		infovv.setLayout(vvPanelLayout);
		vvPanelLayout.setHorizontalGroup(
				vvPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
				.addGap(0, 201, Short.MAX_VALUE)
		);
		vvPanelLayout.setVerticalGroup(
				vvPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
				.addGap(0, 120, Short.MAX_VALUE)
		);

		infoTextArea.setColumns(20);
		infoTextArea.setRows(4);
		infoScrollPane.setViewportView(infoTextArea);

		javax.swing.GroupLayout layout = new javax.swing.GroupLayout(infoPanel);
		infoPanel.setLayout(layout);
		layout.setHorizontalGroup(
				layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
				.addGroup(layout.createSequentialGroup()
						.addComponent(infovv, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
						.addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(infoScrollPane, javax.swing.GroupLayout.DEFAULT_SIZE, 362, Short.MAX_VALUE))
		);
		layout.setVerticalGroup(
				layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
				.addComponent(infovv, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(infoScrollPane, javax.swing.GroupLayout.DEFAULT_SIZE, 110, Short.MAX_VALUE)
		);

		return infoPanel;
	}

	/**
	 * This method will animate the transition between two layouts.
	 *
	 */
	private void animateLayoutChanges(){
		if(!(layout instanceof CircleLayout)){
			Relaxer relaxer = new VisRunner((IterativeContext)layout);
			relaxer.stop();
			relaxer.prerelax();
			StaticLayout<Object,Object> staticLayout =
				new StaticLayout<Object,Object>(g, layout);
			LayoutTransition<Object,Object> lt =
				new LayoutTransition<Object,Object>(vv, vv.getGraphLayout(), staticLayout);
			Animator animator = new Animator(lt);
			animator.start();
		}
	}

	/**
	 * This inner class is used to control the animation of new states
	 * being added to the visualisation.
	 * @author Jerramy Winchester
	 *
	 */
	public class AnimateThread extends Thread{

		DefaultMutableTreeNode rootNode_;

		/** The thread constructor */
		public AnimateThread(JTree tree_){
			rootNode_ = (DefaultMutableTreeNode)tree_.getModel().getRoot();
		}

		public void run(){
			// Expand out all the rows of the tree
			for (int i = 0; i < tree.getRowCount(); i++){
				tree.expandRow(i);
			}
			Enumeration enumRoot = rootNode_.children();
			try{
				// Start the animation
				while(showAnimation_ && enumRoot.hasMoreElements()){
					DefaultMutableTreeNode childNode = (DefaultMutableTreeNode)enumRoot.nextElement();
					Enumeration enumChild = childNode.children();

					while(showAnimation_ && enumChild.hasMoreElements()){
						DefaultMutableTreeNode node = (DefaultMutableTreeNode)enumChild.nextElement();

						if(node.isLeaf()){
							vv.getRenderContext().getPickedVertexState().clear();
							vv.getRenderContext().getPickedEdgeState().clear();

							// TODO this has some strange effects on the repaint
							//      of the tree and ModelJUnit. Fix this later.
							//tree.scrollPathToVisible(new TreePath(node.getPath()));
							//tree.setSelectionPath(new TreePath(node.getPath()));

							Transition nodeInfo = (Transition)node.getUserObject();
							EdgeInfo edge = jView_.getEdge(nodeInfo);

							g.addVertex(edge.getSrcVertex());
							g.addVertex(edge.getDestVertex());
							g.addEdge(edge, edge.getSrcVertex(), edge.getDestVertex());
							vv.getRenderContext().getPickedEdgeState().pick(edge, true);
							vv.getRenderContext().getPickedVertexState().pick(edge.getDestVertex(), true);
							layout.setGraph(g);
							layout.initialize();
							animateLayoutChanges();
						}
						if(animationToggleButton.isSelected()){
							try{
								Thread.sleep(Long.MAX_VALUE);
							} catch (InterruptedException ie){
								//Ignore
							}
						} else {
							Thread.sleep(animationSlider.getValue());
						}
					}
				}

				vv.getRenderContext().getPickedVertexState().clear();
				vv.getRenderContext().getPickedEdgeState().clear();

				// Collapse all the rows of the tree
				for (int i = 1; i < tree.getRowCount(); i++){
					tree.collapseRow(i);
				}
				showAnimation_ = false;
				tree.setSelectionPath(tree.getPathForRow(0));
				g = jView_.getGraph();
				layout.setGraph(g);
				layout.initialize();
				animateLayoutChanges();

			}catch (Exception ex){
				//Ignore
			}
		}
	}
}
