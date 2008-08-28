/**
 * 
 */
package net.sourceforge.czt.modeljunit.gui.visualisaton;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.Graphics2D;
import java.awt.GridLayout;
import java.awt.Paint;
import java.awt.Point;
import java.awt.Stroke;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
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
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollBar;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTextArea;
import javax.swing.JTree;
import javax.swing.LayoutStyle;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.filechooser.FileFilter;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreeSelectionModel;

import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.Transition;
import net.sourceforge.czt.modeljunit.gui.PanelAbstract;

import org.apache.commons.collections15.Predicate;

import edu.uci.ics.jung.algorithms.layout.CircleLayout;
import edu.uci.ics.jung.algorithms.layout.FRLayout2;
import edu.uci.ics.jung.algorithms.layout.GraphElementAccessor;
import edu.uci.ics.jung.algorithms.layout.ISOMLayout;
import edu.uci.ics.jung.algorithms.layout.Layout;
import edu.uci.ics.jung.algorithms.layout.StaticLayout;
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
import edu.uci.ics.jung.visualization.util.PredicatedParallelEdgeIndexFunction;

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
	private VertexFontTransformer<Object, Font> v_vft;
	private VertexLabelTransformer<Object, String> v_vlt;
	private VertexGradientRenderer<Object, Object> v_vgr;
	private VertexStrokeTransformer<Object, Object> v_vst;
	private VertexShapeTransformer<Object> v_vsht;
	private VertexEdgePaintTransformer<Object, Object> v_vept;

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
	private JScrollPane m_scrollTreeArea;
	private JTree tree;	

	// Variables for control panel
	private JButton mergeVerticesButton;
	private JButton expandVerticesButton;
	private JButton mergeEdgesButton;
	private JButton expandEdgesButton;
	private JButton resetButton;
	private JButton captureButton;
	private JButton animationButton;
	private JCheckBox vertLabelCheckBox;
	private JCheckBox edgeLabelCheckBox;
	private JComboBox vertLabelPosComboBox;
	private JComboBox layoutTypeComboBox; 
	private JComboBox explorationComboBox;
	private JLabel vertLabelPos;	
	private JLabel sliderLabel;
	private JPanel labelsPanel;
	private JPanel layoutTypePanel;
	private JPanel mergePanel;
	private JPanel explorationPanel;
	private JPanel capturePanel;
	private JScrollBar explScrollBar;
	// End of variables declaration

	/**
	 * The PanelGraphVisualisation constructor.
	 * This will initialise the panel and also the visualisation.
	 */
	public PanelJUNGVisualisation(){
		jView_ = JUNGHelper.getJUNGViewInstance();

		g = jView_.getGraph();

		layout = new FRLayout2<Object, Object>(jView_.getGraph());

		vv = new VisualizationViewer<Object, Object>(layout);
		vv.setBackground(Color.white);

		//Setup the ability to compress multiple edges into one		
		final PredicatedParallelEdgeIndexFunction<Object, Object> eif = 
			PredicatedParallelEdgeIndexFunction.getInstance();
		exclusions = new HashSet<Object>();
		eif.setPredicate(new Predicate<Object>() {
			public boolean evaluate(Object e) {
				return exclusions.contains(e);
			}});
		vv.getRenderContext().setParallelEdgeIndexFunction(eif);

		//A GraphCollapser to handle merging of vertices.
		collapser = new GraphCollapser(g);

		// Create the custom mouse plugins to control the visualisation	with the mouse	
		PluggableGraphMouse gm = new PluggableGraphMouse(); 
		gm.add(new TranslatingGraphMousePlugin(MouseEvent.BUTTON3_MASK));		
		gm.add(new PickingGraphMousePlugin<Object, Object>());		
		gm.add(new ScalingGraphMousePlugin(new CrossoverScalingControl(), 0, 1.1f, 0.9f));		
		vv.setGraphMouse(gm);
		vv.addMouseListener(this);

		// translate the graph down and across so that it is not hard up
		// against the side of the splitPane box.
		MutableTransformer modelTransformer = vv.getRenderContext().getMultiLayerTransformer().getTransformer(Layer.LAYOUT);
		modelTransformer.translate(25, 25);

		e_eft = new EdgeFontTransformer<Object, Font>();
		e_elt = new EdgeLabelTransformer<Object, String>(vv);
		e_ept = new EdgePaintTransformer<Object, Paint>(new Color(40, 40, 40),Color.black,vv);
		e_est = new EdgeStrokeTransformer<Object, Stroke>();
		v_vft = new VertexFontTransformer<Object, Font>();
		v_vlt = new VertexLabelTransformer<Object, String>();
		v_vgr = new VertexGradientRenderer<Object, Object>(Color.white, vv.getPickedVertexState(), true);
		v_vst = new VertexStrokeTransformer<Object, Object>(jView_.getGraph(), vv.getPickedVertexState());
		v_vsht = new VertexShapeTransformer<Object>();
		v_vept = new VertexEdgePaintTransformer<Object, Object>(vv.getPickedVertexState(), jView_.getVertices());

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

	/** This should be called by the top-level program whenever the
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
	 * This method is used to update the panel. This will be used to show the animation
	 * at a later date.
	 */
	public void updateGUI() {
		updateInfoPanel("Nothing Selected");
		tree.setModel(new DefaultTreeModel(jView_.getRootTreeNode()));		
		layout.setGraph(jView_.getGraph());
		layout.setSize(new Dimension(vizAndInfo.getWidth() - 75
				, vizAndInfo.getHeight() - infoPanel.getHeight() - 75));

		vv.getModel().setGraphLayout(layout, new Dimension(vizAndInfo.getWidth() - 20
				, vizAndInfo.getHeight() - infoPanel.getHeight() - 32));
		vv.getRenderContext().setEdgeFontTransformer(e_eft);
		vv.getRenderContext().setEdgeLabelTransformer(e_elt);
		vv.getRenderContext().setEdgeDrawPaintTransformer(e_ept);
		vv.getRenderContext().setEdgeStrokeTransformer(e_est);
		vv.getRenderContext().setArrowDrawPaintTransformer(e_ept);
		vv.getRenderContext().setArrowFillPaintTransformer(e_ept);
		vv.getRenderContext().setVertexFontTransformer(v_vft);
		vv.getRenderContext().setVertexLabelTransformer(v_vlt);		
		vv.getRenderContext().setVertexStrokeTransformer(v_vst);
		vv.getRenderContext().setVertexShapeTransformer(v_vsht);
		v_vept = new VertexEdgePaintTransformer<Object, Object>(vv.getPickedVertexState(), jView_.getVertices());
		vv.getRenderContext().setVertexDrawPaintTransformer(v_vept);
		vv.getRenderer().setVertexRenderer(v_vgr);

		//Set the curvature in the edges
		AbstractEdgeShapeTransformer<Object, Object> aesf = 
			(AbstractEdgeShapeTransformer<Object, Object>)vv.getRenderContext().getEdgeShapeTransformer();
		aesf.setControlOffsetIncrement(30);
		//Set the new size of the visualisation
		vv.setSize(new Dimension(vizAndInfo.getWidth() - 20
				, vizAndInfo.getHeight() - infoPanel.getHeight() - 30));

		vv.repaint();
	}

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
			str.deleteCharAt(str.length() - 1);
			str.deleteCharAt(str.length() - 1);						
			infoGraph.addVertex(" - Merged States");
			infoLayout.setLocation(" - Merged States", new Point(30, 50));
			infoTextArea.append("Merged states are:\n" + str.toString());
			infoTextArea.setCaretPosition(0);
		} else if(obj instanceof EdgeInfo){	
			String srcVertex = "Source State: " + ((EdgeInfo)obj).getSrcVertex().getName();
			String destVertex = "Destination State: " + ((EdgeInfo)obj).getDestVertex().getName();
			String edge = "                                 Action taken: " + ((EdgeInfo)obj).getAction();
			infoGraph.addVertex(destVertex);
			if(!((EdgeInfo)obj).getSrcVertex().getName().equals(((EdgeInfo)obj).getDestVertex().getName())){
				infoGraph.addVertex(srcVertex);
				infoLayout.setLocation(srcVertex, new Point(30, 20));
				infoGraph.addEdge(edge, srcVertex, destVertex);
			} else {
				infoGraph.addEdge(edge, destVertex, destVertex);
			}						
			infoLayout.setLocation(destVertex, new Point(30, 90));
			infoTextArea.append("Action selected: " + ((EdgeInfo)obj).getAction() + "\n");
			if(((EdgeInfo)obj).getSequences_().size() == 0){
				infoTextArea.append("--------------------------------\nnot tested:\n");
			} else {
				infoTextArea.append("--------------------------------\nused in:\n");
				Iterator<String> itr = ((EdgeInfo)obj).getSequences_().iterator();
				while(itr.hasNext()){
					infoTextArea.append(itr.next()+ "\n");
				}
			}
			infoTextArea.setCaretPosition(0);
		} else {			
			infoTextArea.append(obj.toString() + "\n");
		}

		infovv.repaint();
	}

	@SuppressWarnings("unchecked")
	@Override
	public void actionPerformed(ActionEvent e) {
		AbstractButton source = (AbstractButton)e.getSource();
		// The show vertex labels checkbox
		if (source == vertLabelCheckBox){			
			v_vlt.setShowLabels(vertLabelCheckBox.isSelected());

			// The show edge label checkbox
		} else if (source == edgeLabelCheckBox){
			e_elt.showEdgeLabels(edgeLabelCheckBox.isSelected());

			// Merge vertices button
		} else if (source == mergeVerticesButton){
			Collection<VertexInfo> picked = new HashSet(vv.getPickedVertexState().getPicked());				
			/*if(layout instanceof ISOMLayout || layout instanceof CircleLayout){
				String multiLineMsg[] = { "The ISOM and Circle layout types do not support merging vertices. "
						, "Please select another layout type and try again."} ;
				JOptionPane.showMessageDialog(m_panelGraph, multiLineMsg);
			} else*/ if(picked.size() > 1) {
				Graph<Object, Object> inGraph = layout.getGraph();
				Graph<Object, Object> clusterGraph = collapser.getClusterGraph(inGraph, picked);
				Graph<Object, Object> graph = collapser.collapse(layout.getGraph(), clusterGraph);
				double sumx = 0;
				double sumy = 0;
				for(Object v : picked) {						
					Point2D p = (Point2D)layout.transform(v);
					sumx += p.getX();
					sumy += p.getY();
				}
				Point2D cp = new Point2D.Double(sumx/picked.size(), sumy/picked.size());
				vv.getRenderContext().getParallelEdgeIndexFunction().reset();					                    
				layout.setGraph(graph);
				layout.setLocation(clusterGraph, cp);
				vv.getPickedVertexState().clear();				
			}

			// Expand vertices button
		} else if (source == expandVerticesButton){
			Collection<VertexInfo> picked = new HashSet(vv.getPickedVertexState().getPicked());
			for(Object v : picked) {
				if(v instanceof Graph) {
					Graph<Object, Object> graph = collapser.expand(layout.getGraph(), (Graph<VertexInfo, EdgeInfo>)v);
					vv.getRenderContext().getParallelEdgeIndexFunction().reset();
					layout.setGraph(graph);
				}
				vv.getPickedVertexState().clear();
				updateInfoPanel("Nothing Selected");
			}


		} else if (source == mergeEdgesButton){
			Collection<Object> picked = vv.getPickedVertexState().getPicked();
			if(picked.size() == 2) {					
				Pair<Object> pair = new Pair<Object>(picked);
				Graph<Object, Object> graph = layout.getGraph();
				Collection<Object> edges = new HashSet<Object>(graph.getIncidentEdges(pair.getFirst()));
				edges.retainAll(graph.getIncidentEdges(pair.getSecond()));					
				exclusions.addAll(edges);				
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
			//layout.setGraph(g);
			Collection<Object> vertices = layout.getGraph().getVertices();
			for(Object v : vertices) {
				if(v instanceof Graph) {
					System.out.println("getting here");
					Graph<Object, Object> graph = collapser.expand(layout.getGraph(), (Graph<VertexInfo, EdgeInfo>)v);
					vv.getRenderContext().getParallelEdgeIndexFunction().reset();
					layout.setGraph(graph);
				}
				vv.getPickedVertexState().clear();
				updateInfoPanel("Nothing Selected");
			}
			exclusions.clear();

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
		}
	}

	@Override
	public void mouseReleased(MouseEvent e) {		
	}	

	private JPanel getControlPanel() {
		JPanel panel = new JPanel();
		labelsPanel = new JPanel();
		vertLabelCheckBox = new JCheckBox();
		edgeLabelCheckBox = new JCheckBox();		
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
		explorationPanel = new JPanel();
		captureButton = new JButton();
		capturePanel = new JPanel();
		sliderLabel = new JLabel();
		explScrollBar = new JScrollBar();
		explorationComboBox = new JComboBox();
		animationButton = new JButton();

		labelsPanel.setBorder(BorderFactory.createTitledBorder("Labels"));

		vertLabelCheckBox.setText("Show vertex labels");
		vertLabelCheckBox.addActionListener(this);
		vertLabelCheckBox.setSelected(true);

		edgeLabelCheckBox.setText("Show edge labels");
		edgeLabelCheckBox.addActionListener(this);

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
				jPanel1Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(jPanel1Layout.createSequentialGroup()
						.addGroup(jPanel1Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
								.addComponent(vertLabelCheckBox)
								.addGroup(jPanel1Layout.createSequentialGroup()
										.addComponent(vertLabelPos)
										.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
										.addComponent(vertLabelPosComboBox, 0, 68, Short.MAX_VALUE))

										.addComponent(edgeLabelCheckBox))
										.addContainerGap())
		);
		jPanel1Layout.setVerticalGroup(
				jPanel1Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(jPanel1Layout.createSequentialGroup()
						.addComponent(vertLabelCheckBox)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addGroup(jPanel1Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
								.addGroup(jPanel1Layout.createParallelGroup(GroupLayout.Alignment.BASELINE)
										.addComponent(vertLabelPos)
										.addComponent(vertLabelPosComboBox, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE))
										.addGroup(jPanel1Layout.createSequentialGroup()
												.addGap(25, 25, 25)
												.addGroup(jPanel1Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
														.addComponent(edgeLabelCheckBox))))
														.addContainerGap(GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
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
						l.setInitializer(vv.getGraphLayout());
						l.setSize(vv.getSize());
						LayoutTransition<Object, Object> lt =
							new LayoutTransition<Object, Object>(vv, vv.getGraphLayout(), l);
						Animator animator = new Animator(lt);
						animator.start();
						vv.getRenderContext().getMultiLayerTransformer().setToIdentity();						
						vv.repaint();
						layout = l;
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
				.addComponent(mergeEdgesButton, GroupLayout.DEFAULT_SIZE, 151, Short.MAX_VALUE)
				.addComponent(expandEdgesButton, GroupLayout.DEFAULT_SIZE, 151, Short.MAX_VALUE)
				.addComponent(resetButton, GroupLayout.DEFAULT_SIZE, 151, Short.MAX_VALUE)
		);
		jPanel3Layout.setVerticalGroup(
				jPanel3Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(jPanel3Layout.createSequentialGroup()
						.addComponent(mergeVerticesButton)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(expandVerticesButton)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(mergeEdgesButton)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED, 7, Short.MAX_VALUE)
						.addComponent(expandEdgesButton)
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(resetButton)
						.addContainerGap())
		);

		explorationPanel.setBorder(BorderFactory.createTitledBorder("Capture"));

		captureButton.setText("Save as image");
		captureButton.addActionListener(this);

		GroupLayout jPanel4Layout = new GroupLayout(explorationPanel);
		explorationPanel.setLayout(jPanel4Layout);
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

		capturePanel.setBorder(BorderFactory.createTitledBorder("Show Exploration"));

		sliderLabel.setText("test sequences");

		animationButton.setText("Start");

		explorationComboBox.setModel(new javax.swing.DefaultComboBoxModel(new String[] { "Item 1", "Item 2", "Item 3", "Item 4" }));

		explScrollBar.setOrientation(JScrollBar.HORIZONTAL);

		GroupLayout jPanel5Layout = new GroupLayout(capturePanel);
		capturePanel.setLayout(jPanel5Layout);
		jPanel5Layout.setHorizontalGroup(
				jPanel5Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(jPanel5Layout.createSequentialGroup()
						.addComponent(sliderLabel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
						.addContainerGap())
						.addComponent(explScrollBar, GroupLayout.DEFAULT_SIZE, 178, Short.MAX_VALUE)
		);
		jPanel5Layout.setVerticalGroup(
				jPanel5Layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addGroup(jPanel5Layout.createSequentialGroup()
						.addComponent(sliderLabel)
						.addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(explScrollBar, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
						.addContainerGap(23, Short.MAX_VALUE))
		);
		GroupLayout layout = new GroupLayout(panel);
		panel.setLayout(layout);
		layout.setHorizontalGroup(
				layout.createParallelGroup(GroupLayout.Alignment.LEADING)
				.addComponent(layoutTypePanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(labelsPanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(mergePanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(explorationPanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
				.addComponent(capturePanel, GroupLayout.DEFAULT_SIZE, GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
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
						.addPreferredGap(LayoutStyle.ComponentPlacement.RELATED)
						.addComponent(explorationPanel, GroupLayout.PREFERRED_SIZE, GroupLayout.DEFAULT_SIZE, GroupLayout.PREFERRED_SIZE)
						.addContainerGap())
		);
		return panel;
	}	

	/**
	 * This method will return the tree panel for the left side of the visualisation.
	 * @return	JPanel The panel containing the tree and associated controls.
	 */
	private JPanel getTreeControls(){		
		JPanel panel;
		JButton expandButton;
		JButton collapseButton;

		//create the tree control.
		tree = new JTree(jView_.getRootTreeNode());
		tree.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
		tree.addTreeSelectionListener(new TreeSelectionListener(){
			@SuppressWarnings("unchecked")
			public void valueChanged(TreeSelectionEvent e) {
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

		// create expandButton.
		expandButton = new JButton("Expand All");				
		expandButton.addActionListener(new ActionListener(){
			public void actionPerformed(final ActionEvent e){								
				for (int i = 0; i < tree.getRowCount(); i++){
					tree.expandRow(i);
				}
			}			
		});

		// create collapseButton
		collapseButton = new JButton("Collapse All");				
		collapseButton.addActionListener(new ActionListener(){
			public void actionPerformed(final ActionEvent e){
				for (int i = 1; i < tree.getRowCount(); i++){					
					tree.collapseRow(i);
				}				
			}
		});
		// position the buttons using a panel
		JPanel treeButtonPanel = new JPanel(new GridLayout(0,2));
		treeButtonPanel.add(expandButton);
		treeButtonPanel.add(collapseButton);

		// setup the tree scroll area
		m_scrollTreeArea = new JScrollPane(tree);
		m_scrollTreeArea.setMinimumSize(new Dimension(200,200));

		// attach everything to the panel
		panel = new JPanel(new BorderLayout());				
		panel.add(treeButtonPanel, BorderLayout.NORTH);		
		panel.add(m_scrollTreeArea, BorderLayout.CENTER);

		return panel;
	}

	private JPanel getInfoPanel(){		
		infoGraph = new DirectedSparseMultigraph<Object, Object>();

		infoLayout = new StaticLayout<Object, Object>(infoGraph);

		infovv = new VisualizationViewer<Object, Object>(infoLayout, new Dimension(200,100));		
		infovv.getRenderContext().setVertexLabelTransformer(new InfoLabelTransformer<Object, Object>());
		infovv.getRenderContext().setEdgeLabelTransformer(new InfoLabelTransformer<Object, Object>());
		infovv.getRenderContext().getEdgeLabelRenderer().setRotateEdgeLabels(false);
		infovv.getRenderContext().setEdgeLabelClosenessTransformer(new ConstantDirectionalEdgeValueTransformer<Object, Object>(.2, .2));
		infovv.getRenderer().getVertexLabelRenderer().setPosition(Renderer.VertexLabel.Position.E);
		infovv.getRenderer().setVertexRenderer(
				new GradientVertexRenderer<Object,Object>(
						Color.white, Color.red, 
						Color.white, Color.red,
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
}
