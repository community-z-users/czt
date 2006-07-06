package support.gui;

import java.awt.event.*;
import java.io.*;
import support.*;
import java.awt.Label;
import jdsl.graph.algo.InvalidQueryException;
import algo.FlightDijkstra;
import jdsl.graph.api.*;
import java.awt.Choice;
import jdsl.core.api.Dictionary;
import java.net.URL;
import java.net.MalformedURLException;

/**
 * This is the Listener class for all the listeners needed for the
 * Flights example GUI. Which listeners it is is determined during
 * the construction.
 *
 * @author Galina Shubina (gs)
 * @version JDSL 2
 */

public class FlightListener implements ActionListener, ItemListener {
  
  /**
   * Type indicating this is a listener for a Query button.
   */
  public static final int FL_QUERY = 0;

  /**
   * Type indicating this is a listener for a Quit button.
   */
  public static final int FL_QUIT = 1;

  /**
   * Type indicating this is a listener for a Checkbox loading 
   * the smallest data set.
   */
  public static final int FL_SMALLER = 2;
  
  /**
   * Type indicating this is a listener for a Checkbox loading 
   * the second smallest data set.
   */
  public static final int FL_SMALL = 3;

  /**
   * Type indicating this is a listener for a Checkbox loading
   * medium data set.
   */
  public static final int FL_MEDIUM = 4;

  /**
   * Type indicating this is a listener for a Checkbox loading
   * large data set.
   */
  public static final int FL_LARGE = 5;

  /**
   * Type indicating this is a listener for a Button clearing the query parameters.
   */
  public static final int FL_CLEAR = 6;
  
  /**
   * Type indicating this is a listener for selecting hour of query start.
   */
  public static final int FL_HOUR = 7;

  /**
   * Type indicating this is a listener for a selecting minute of query start.
   */
  public static final int FL_MINUTE = 8;

  /**
   * Type indicating this is a listener for a selecting time of query start (am or pm).
   */
  public static final int FL_AMPM = 9;

  /**
   * Variable the marks the maxium type number that can be created using this class.
   */
  public static final int FL_MAX = 10;

  /**
   * Variable that indicates the minimum type that controls data set checkboxes.
   */
  public static final int FL_ITEM_FIRST = 2;

  /**
   * Variable that indicates the maximum type that controls data set checkboxes.
   */
  public static final int FL_ITEM_LAST = 5;

  /**
   * Indicates the type of the listener it is. It should be on of the FL_* variables.
   */
  private int type_;

  /**
   * Data set graph. This variable has to be set only for some of the listeners.
   */
  private Graph dataSet_;

  /**
   * Query data. This variable has to be set only for some of the listeners.
   */
  private QueryData queryData_;

  /**
   * Main GUI controller. It is necessary here so that other components of the GUI
   * can be updated when methods of the listener change data sets or query data.
   */
  private FlightPanel updatePanel_;

  /**
   * There can be one label to which we can print the text result of the listener's
   * action, and this is it.
   */
  private Label statusLabel_;

  /**
   * Vertex (city) file location for listeners that load data sets.
   */
  private String vertexFile_;

  /**
   * Edge (flight) file location for listeners that load data sets.
   */
  private String edgeFile_;

  /**
   * Document base for the applet version of this GUI.
   */
  private String docBase_;

  /**
   * Constructs any listener other then checkboxes for data set choice.
   *
   * @param <code>type</code> of the listener. Must be one of FL_*
   * @param <code>dataset</code> data set graph that is to be modified, can be null
   * @param <code>querydata</code> query data to be modified, can be null
   * @param <code>fpanel</code> main controller
   * @param <code>statuslabel</code> where to put text indicating changes
   */
  public FlightListener(int type, Graph dataset, QueryData querydata, FlightPanel fpanel, Label statuslabel) {
    if (type < 0 || type >= FL_MAX) {
      System.out.println("Invalid Listener Type");
      type_ = -1;
      return;
    }
    type_ = type;
    dataSet_ = dataset;
    queryData_ = querydata;
    updatePanel_ = fpanel;
    statusLabel_ = statuslabel;
  }

  /**
   * Constructs any listeners for the checkboxes making data set choices.
   *
   * @param <code>type</code> of the listener. Must be one of FL_*
   * @param <code>dataset</code> data set graph that is to be modified, can be null
   * @param <code>querydata</code> query data to be modified, can be null
   * @param <code>fpanel</code> main controller
   * @param <code>statuslabel</code> where to put text indicating changes
   * @param <code>vfile</code> file of vertices of this dataset
   * @param <code>efile</code> file of edges of this dataset
   * @param <code>docBase</code> null if this is an application, document base otherwise.
   */
  public FlightListener(int type, Graph dataset, QueryData querydata, FlightPanel fpanel, Label statuslabel, String vfile, String efile, String docBase) {
    this(type,dataset,querydata,fpanel,statuslabel);

    vertexFile_ = vfile;
    edgeFile_ = efile;
    docBase_ = docBase;
  }

  /**
   * If this is a FL_QUERY, FL_QUIT, or FL_CLEAR listener, it demultiplexes
   * to perform the appropriate action.
   */
  public void actionPerformed(ActionEvent ae) {

    switch(type_) {
    case FL_QUERY:
      query();
      break;
    case FL_QUIT:
      quit();
      break;
    case FL_CLEAR:
      clear();
      break;
    default:
      System.out.println("Invalid Listener");
      return;
    }
  }


  /**
   * If this is either a checkbox for datasets or 
   * a choice for time when a query should be executed, it demultiplexes
   * to perform the appropriate action.
   */
  public void itemStateChanged(ItemEvent e) {

    if ((type_ >= FL_ITEM_FIRST && type_ <= FL_ITEM_LAST)) {
      loadDataset();
      queryData_.setFrom(null);
      queryData_.setTo(null);
      queryData_.setPath(null);

      updatePanel_.updatedDataSet();
      updatePanel_.updatedQueryData();
      return;
    }

    Choice c = (Choice)e.getItemSelectable();

    switch(type_) {
    case FL_HOUR:
      queryData_.setHour(c.getSelectedIndex()+1);
      break;
    case FL_MINUTE:
      queryData_.setMinute(c.getSelectedIndex()*5);
      break;
    case FL_AMPM:
      queryData_.setAmpm(c.getSelectedIndex());
      break;
    default:
      System.out.println("Invalid Item Listener");
      return;
    }

  }

  /**
   * Loads the appropriate dataset from <code>vertexFile_</code> and
   * <code>edgeFile_</code>. Must be one of checkbox data set listeners.
   */
  private void loadDataset() {
    Parser.removeAllEdges(dataSet_);
    Parser.removeAllVertices(dataSet_);
    Dictionary d = null;
    try {
      if (docBase_ != null) {
	d = Parser.parseVertices(new URL(docBase_.toString() + vertexFile_), dataSet_);
      } else {
	d = Parser.parseVertices(vertexFile_, dataSet_);
      }
    } catch (MalformedURLException mue) {
      statusLabel_.setText("Cannot load airport url");
    } catch (FileNotFoundException fnfe) {
      statusLabel_.setText("Airports file not found");
      System.out.println("Cannot load airports: file " + vertexFile_ + " does not exist.");
      return;
    } catch (FlightException fe) {
      statusLabel_.setText("Error loading airports");
      System.out.println("File " + vertexFile_ +": " + fe.getMessage());
      return;
    }

    if (d == null) {
      return;
    }

    try {
      if (docBase_ != null) {
	Parser.parseEdges(new URL(docBase_.toString() + edgeFile_), dataSet_, d);
      } else {
	Parser.parseEdges(edgeFile_, dataSet_, d);
      }
    }  catch (MalformedURLException mue) {
      statusLabel_.setText("Cannot load flights url");
    } catch (FileNotFoundException fnfe) {      
      statusLabel_.setText("Flights file not found");
      System.out.println("Cannot load flights: file " + edgeFile_ + " does not exist.");
      return;
    } catch (FlightException fe) {
      statusLabel_.setText("Error loading flights");
      System.out.println("File " + edgeFile_ +": " + fe.getMessage());
      return;
    }

    statusLabel_.setText(dataSet_.numVertices() + " cities; " + dataSet_.numEdges() + " flights");
  }

  /**
   * Performs the actual query according to information in <code>dataSet_</code>
   * and <code>queryData_</code>. This is where <code>FlightDijkstra</code> class
   * gets instantiated.
   * 
   * @see FlightDijkstra
   */
  private void query() {
    Vertex from,to;
    from = queryData_.getFrom();
    to = queryData_.getTo();

    if (from == null) {
      statusLabel_.setText("Cannot perform query: missing origin and destination");
      return;
    }
    if (to == null) {
      statusLabel_.setText("Cannot perform query: missing destination");
      return;
    }

    FlightDijkstra alg = new FlightDijkstra();
    
    int time = (queryData_.getHour()%12) * 60 + queryData_.getMinute();
    if (queryData_.getAmpm() == QueryData.QD_PM) {
      time += 60*12;
    }

    time = StandardOps.toGMT(time, ((AirportSpecs)from.element()).GMToffset());

    alg.execute(dataSet_, from, to, time);

    try {
      queryData_.setPath(alg.reportPath());
      int t = alg.distance(to);
 
      statusLabel_.setText("Path of length " + ((t - (t%60))/60) + " hours " + (t%60) + " minutes found");
    } catch (InvalidQueryException iqe){
      statusLabel_.setText("No path exists between " + ((AirportSpecs)from.element()).code() +
			   " and " + ((AirportSpecs)to.element()).code());
      queryData_.setFrom(null);
      queryData_.setTo(null);
    }

    alg.cleanup();
    updatePanel_.updatedQueryData();
  }

  /**
   * Quits the application. Called by listener of FL_QUIT type.
   */
  private void quit() {
    System.exit(0);
  }

  /**
   * Clears the query parameters (hour, minute, and old path). Called
   * by listener of FL_CLEAR type.
   */
  private void clear() {
    queryData_.setFrom(null);
    queryData_.setTo(null);
    queryData_.setPath(null);
    updatePanel_.updatedQueryData();
  }

}
							
