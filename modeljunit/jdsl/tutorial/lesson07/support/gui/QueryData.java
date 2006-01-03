package support.gui;

import jdsl.graph.api.Edge;
import jdsl.graph.api.Vertex;
import jdsl.graph.api.EdgeIterator;
import java.awt.List;
import support.*;

public class QueryData {
  
  public static final int QD_HOURS = 12;
  public static final int QD_HOURINCR = 1;
  public static final int QD_MINUTES = 59;
  public static final int QD_MININCR = 5;

  public static final int QD_AM = 0;
  public static final int QD_PM = 1;
  public static final int QD_MAX = 2;
  public static final String[] ampmLabels_ = {
    "AM",
    "PM"
  };
  
  private int hour_;
  private int minute_;
  private int ampm_;
  private Vertex from_;
  private Vertex to_;

  private EdgeIterator path_;
  private List itinerary_;

  public QueryData() {
    setHour(1);
    setMinute(0);
    setAmpm(QD_AM);
  }

  public QueryData(int hour, int minute, int ampm) {
    setHour(hour);
    setMinute(minute);
    setAmpm(ampm);
  }

  public void setHour(int hour) { hour_ = hour; }
  public void setMinute(int minute) { minute_ = minute; }
  public void setAmpm(int ampm) { ampm_ = ampm; }
  public void setFrom(Vertex from) { from_ = from; }
  public void setTo(Vertex to) { to_ = to; }
  public void setPath(EdgeIterator eiter) { 
    path_ = eiter; 
    
    if (itinerary_ == null) {
      return;
    }

    if (path_ != null) {
      itinerary_.removeAll();
      for( ; path_.hasNext() ; ) {
	Edge e = path_.nextEdge();
	FlightSpecs fs = (FlightSpecs)e.element();

	itinerary_.add(fs.label());
      }
      path_.reset();
    } else {
      itinerary_.removeAll();
    }
  }
  
  public void setItineraryList(List list) {
    itinerary_ = list;
  }

  public int getHour() { return hour_; }
  public int getMinute() { return minute_; }
  public int getAmpm() { return ampm_; }
  public Vertex getFrom() { return from_; }
  public Vertex getTo() { return to_; }

  public EdgeIterator queryPath() {
    return path_;
  }

}
