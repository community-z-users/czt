package support.gui;

import jdsl.core.api.*;
import jdsl.core.ref.*;
import jdsl.graph.algo.*;
import jdsl.graph.api.*;
import jdsl.graph.ref.*;
import java.awt.*;
import java.awt.event.*;
import support.*;
import java.net.URL;

public class FlightPanel extends Panel {
  
  private CheckboxGroup datasetGroup_;
  private Checkbox[] datasetCheckboxes_;
  
  public static final int DS_ULTRA_SMALL = 0;
  public static final int DS_SMALL = 1;
  public static final int DS_MEDIUM = 2;
  public static final int DS_LARGE = 3;
  public static final int DS_MAX = 4;

  public static final int  WIDTH = 850;
  public static final int  STATUS_HEIGHT = 27;
  public static final int  HEIGHT = MapCanvas.HEIGHT + 18;


  public static String[] datasetLabels_ = {
    "Smaller",
    "Small",
    "Medium",
    "Large"
  };

  public static final String[] vertexFiles_ = {
    "support/data/ultrasparse_graph.dat",
    "support/data/sparse_graph.dat",
    "support/data/graph.dat",
    "support/data/full_graph.dat"
  };

  public static final String[] edgeFiles_ = {
    "support/data/ultrasparse_flights.dat",
    "support/data/sparse_flights.dat",
    "support/data/flights.dat",
    "support/data/full_flights.dat"
  };


  private Label datasetStat_ = new Label("Not initialized",Label.LEFT);

  private Choice hourChoice_;
  private Choice minuteChoice_;
  private Choice ampmChoice_;

  private Label fromLabel_ = new Label("From: ", Label.LEFT);
  private Label toLabel_ = new Label("To: ", Label.LEFT);

  private Button queryButton_ = new Button("Query");
  private Button quitButton_ = new Button("Quit");
  private Button clearButton_ = new Button("Clear");

  private QueryData queryData_;
  private Graph graph_ = new IncidenceListGraph();

  private List itinerary_;

  private MapCanvas mapCanvas_;
  private Label mapStatusLabel_;

  private String docBase_;

  public FlightPanel() {
    super();

    queryData_ = new QueryData();
 
    init();    
    
    setSize(WIDTH, HEIGHT);

  }

  public FlightPanel(String docBase) {
    super();

    queryData_ = new QueryData();
    graph_ = new IncidenceListGraph();

    docBase_ = docBase;

    init();
    
    setSize(WIDTH, HEIGHT);

    doLayout();

  }
  
  public void updatedDataSet() {
    updatedDataSet(true);
  }

  public void updatedDataSet(boolean val) {
    if (val) {
      mapCanvas_.forceUpdate();
    }
  }

  public void updatedQueryData() {
    Vertex v = queryData_.getFrom();
    if (v == null) {
      fromLabel_.setText("From: ");
    } else {
      fromLabel_.setText("From: " + ((AirportSpecs)(v.element())).code());
    }
    v = queryData_.getTo();
    if (v == null) {
      toLabel_.setText("To: ");
    } else {
      toLabel_.setText("To: " + ((AirportSpecs)(v.element())).code());
    }

    mapCanvas_.forceUpdate();
  }

  private void init() {
    setLayout(new BorderLayout());
    
    
    Panel allMenuPanel = new Panel(new BorderLayout()) {
      public Insets getInsets() {
	return new Insets(25,10,25,20);
      };
    };

    itinerary_ = new List();
    Font listFont = new Font("Monospaced",Font.PLAIN,11);
    itinerary_.setFont(listFont);
    //    FontMetrics fm = itinerary_.getGraphics().getFontMetrics(listFont);


    queryData_.setItineraryList(itinerary_);
    
    //    allMenuPanel.add(itinerary_,BorderLayout.CENTER);
    
    Panel dsPanel = new Panel(new GridLayout(5,1));

    Label headerLabel = new Label("Choose Data Set");
    headerLabel.setForeground(Color.red.darker());

    dsPanel.add(headerLabel);
    Panel oneRow = null;
    datasetGroup_ = new CheckboxGroup();
    datasetCheckboxes_ = new Checkbox[DS_MAX];
    for(int i=0; i<DS_MAX; i++) {
      datasetCheckboxes_[i] = new Checkbox(datasetLabels_[i], false, datasetGroup_);
      datasetCheckboxes_[i].addItemListener(new FlightListener(i + FlightListener.FL_ITEM_FIRST,
							       graph_,
							       queryData_,
							       this,
							       datasetStat_,
							       vertexFiles_[i],
							       edgeFiles_[i],
							       docBase_
							       ));
      if (i%2 == 0) {
	oneRow = new Panel(new GridLayout(1,2));
      }
      oneRow.add(datasetCheckboxes_[i]);
      if (i%2 == 1) {
	dsPanel.add(oneRow);
      }
    }
    dsPanel.add(datasetStat_);
    headerLabel = new Label("Choose Query Parameters");
    headerLabel.setForeground(Color.red.darker());
    dsPanel.add(headerLabel);

    allMenuPanel.add(dsPanel,BorderLayout.NORTH);

    Panel timeAndQueryPanel = new Panel(new BorderLayout());

    Panel queryPanel = new Panel(new GridLayout(3,1));

    hourChoice_ = new Choice();
    minuteChoice_ = new Choice();
    ampmChoice_ = new Choice();

    String toAdd;
    for(int i=1; i<=QueryData.QD_HOURS; i = i + QueryData.QD_HOURINCR) {
      toAdd = "" + i;
      if (toAdd.length() == 1) toAdd = "0" + toAdd;
      hourChoice_.add(toAdd);
    }
    for(int i=0; i<=QueryData.QD_MINUTES; i = i + QueryData.QD_MININCR) {
      toAdd = "" + i;
      if (toAdd.length() == 1) toAdd = "0" + toAdd;
      minuteChoice_.add(toAdd);
    }
    for(int i=0; i<QueryData.QD_MAX; i++) {
      ampmChoice_.add(QueryData.ampmLabels_[i]);
    }


    hourChoice_.addItemListener(new FlightListener(FlightListener.FL_HOUR,
						   null, queryData_,this,null));
    minuteChoice_.addItemListener(new FlightListener(FlightListener.FL_MINUTE,
						   null, queryData_,this,null));
    ampmChoice_.addItemListener(new FlightListener(FlightListener.FL_AMPM,
						   null, queryData_,this,null));

    oneRow = new Panel(new GridLayout(1,3));
    oneRow.add(hourChoice_);

    oneRow.add(minuteChoice_);
    oneRow.add(ampmChoice_);
    timeAndQueryPanel.add(oneRow, BorderLayout.NORTH);
    //    queryPanel.add(oneRow);

    headerLabel = new Label("Click on the map to select:");
    queryPanel.add(headerLabel);

    queryPanel.add(fromLabel_);
    queryPanel.add(toLabel_);
    
    oneRow = new Panel(new FlowLayout());
    oneRow.add(clearButton_);
    oneRow.add(queryButton_);

    timeAndQueryPanel.add(queryPanel,BorderLayout.CENTER);

    if (docBase_ == null) {
      oneRow.add(quitButton_);
    }

    timeAndQueryPanel.add(oneRow, BorderLayout.SOUTH);

    Panel bottomPanel = new Panel(new BorderLayout());
    bottomPanel.add(timeAndQueryPanel,BorderLayout.NORTH);
    bottomPanel.add(itinerary_,BorderLayout.CENTER);

    allMenuPanel.add(bottomPanel,BorderLayout.CENTER);

    add(allMenuPanel, BorderLayout.EAST);    

    mapStatusLabel_ = new Label("Not initialized");
    Panel mapPanel = new Panel(new BorderLayout());

    if (docBase_ == null) {
      mapCanvas_ = new MapCanvas(graph_,queryData_,this,mapStatusLabel_);
    } else {
      mapCanvas_ = new MapCanvas(graph_,queryData_,this,mapStatusLabel_,docBase_);
    }

    mapPanel.add(mapCanvas_,BorderLayout.CENTER);
    mapPanel.add(mapStatusLabel_,BorderLayout.SOUTH);

    add(mapPanel, BorderLayout.CENTER);
   
    clearButton_.addActionListener(new FlightListener(FlightListener.FL_CLEAR,
						      graph_,queryData_,this, 
						      null));
    queryButton_.addActionListener(new FlightListener(FlightListener.FL_QUERY,
						      graph_,queryData_,this, mapStatusLabel_));
    quitButton_.addActionListener(new FlightListener(FlightListener.FL_QUIT,
						     null,null,null,null));

  }

}
