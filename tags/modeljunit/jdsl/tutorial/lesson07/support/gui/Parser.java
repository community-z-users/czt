package support.gui;

import jdsl.core.api.*;
import jdsl.core.ref.*;
import jdsl.graph.algo.*;
import jdsl.graph.api.*;
import jdsl.graph.ref.*;
import java.io.*;
import support.*;
import java.net.URL;


/**
 * Helper class that has static functions that can parse data sets
 * into flights graph, and manupulate it otherwise.
 *
 * @version JDSL 2
 */
public class Parser {

  private static final int TT_WORD = StreamTokenizer.TT_WORD;
  private static final int TT_NUMBER = StreamTokenizer.TT_NUMBER;


  /**
   * Removes all edges from a graph.
   *
   * @param <code>g</code> A graph
   */
  static public void removeAllEdges(Graph g) {
    for(EdgeIterator pi = g.edges(); pi.hasNext();) {
      g.removeEdge((Edge)pi.nextEdge());
    }
  }

  /**
   * Removes all vertices from a graph.
   *
   * @param <code>g</code> A graph
   */
  static public void removeAllVertices(Graph g) {
    for(VertexIterator vi = g.vertices(); vi.hasNext(); ) {
      g.removeVertex((Vertex)vi.nextVertex());
    }

  }

  static public void parseGraph(String vFile, String eFile, Graph g) 
    throws FileNotFoundException, FlightException {
      Dictionary airportToVertex = Parser.parseVertices(vFile, g);
      Parser.parseEdges(eFile, g, airportToVertex);
  }

  static public void parseGraph(URL vURL, URL eURL, Graph g) 
    throws FileNotFoundException, FlightException {
      Dictionary airportToVertex = Parser.parseVertices(vURL, g);
      Parser.parseEdges(eURL, g, airportToVertex);
  }

  /**
   * Parses vertices from a file into a graph.
   *
   * @param <code>filename</code> Name of the source file
   * @param <code>g</code> A graph 
   * 
   * @return <code>Dictionary</code> mapping airport codes to vertices
   */
  static public Dictionary parseVertices(String filename, Graph g) 
    throws FileNotFoundException, FlightException {

      Reader reader = new BufferedReader(new FileReader(filename));
      return Parser.parseVertices(reader, g);
  }

  /**
   * Parses vertices from a URL into a graph.
   *
   * @param <code>url</code> Source URL
   * @param <code>g</code> A graph
   * 
   * @return <code>Dictionary</code> mapping airport codes to vertices
   */
  static public Dictionary parseVertices(URL url, Graph g) 
    throws FileNotFoundException, FlightException {
    InputStream is = null;
    try {
      is = url.openStream();
    } catch(IOException e) {
      throw new FlightException("IO Error: cannot read from URL " + url.toString());
    }
    Reader reader = new BufferedReader(new InputStreamReader(is));
    return Parser.parseVertices(reader, g);
  }

  /**
   * Parses vertices into a graph.
   *
   * @param <code>reader</code> Source reader
   * @param <code>g</code> A graph
   * 
   * @return <code>Dictionary</code> mapping airport codes to vertices
   */
  static public Dictionary parseVertices(Reader reader, Graph g) 
    throws FileNotFoundException, FlightException {
    StreamTokenizer toker = new AirportTokenizer(reader);
    HashComparator comp = new jdsl.core.ref.ObjectHashComparator();
    Dictionary airportToVertex = new jdsl.core.ref.HashtableDictionary(comp);
    
    AirportSpecs spec;
    try {
      skipLeadingNewlines(toker);
      while(toker.ttype != toker.TT_EOF) {
        spec = Parser.parseAirport(toker);
        airportToVertex.insert(spec.code(), g.insertVertex(spec));
        skipLeadingNewlines(toker);
      }
    }
    catch(IOException e) {
      removeAllVertices(g);
      throw new FlightException("IO Error at line " + toker.lineno() +
                                ": " + e.getMessage());
    }
    
    return airportToVertex;
  }

  /** 
   * Parses edges from a URL into a graph.
   *
   * @param <code>url</code> A source URL
   * @param <code>g</code> A graph
   * @param <code>airportToVertex</code> Dictionary mapping airports to vertices
   */
  static public void parseEdges(URL url, Graph g, Dictionary airportToVertex) 
    throws FileNotFoundException, FlightException {
      InputStream is = null;
    try {
      is = url.openStream();
    } catch(IOException e) {
      throw new FlightException("IO Error: cannot read from URL " + url.toString());
    }
    Reader reader = new BufferedReader(new InputStreamReader(is));
    Parser.parseEdges(reader, g, airportToVertex);

  }

  /**
   * Parses edges from a file into a graph.
   *
   * @param <code>filename</code> Source filename
   * @param <code>g</code> A graph
   * @param <code>airportToVertex</code> Dictionary mapping airports to vertices
   */
  static public void parseEdges(String filename, Graph g, Dictionary airportToVertex) 
    throws FileNotFoundException, FlightException {
      
      Reader reader = new BufferedReader(new FileReader(filename));
      parseEdges(reader, g, airportToVertex);
  }

  /**
   * Parses edges into a graph.
   *
   * @param <code>reader</code> Source reader
   * @param <code>g</code> A graph
   * @param <code>airportToVertex</code> Dictionary mapping airports to vertices
   */
  static public void parseEdges(Reader reader, Graph g, Dictionary airportToVertex) 
    throws FileNotFoundException, FlightException {
     
      StreamTokenizer toker = new FlightTokenizer(reader);

      FlightSpecs spec;
      Vertex from, to;

      try {
        skipLeadingNewlines(toker);
        while(toker.ttype != toker.TT_EOF) {
          spec = Parser.parseFlight(toker, airportToVertex);
          from = (Vertex)(airportToVertex.find(spec.originCode()).element());
          to = (Vertex)(airportToVertex.find(spec.destinationCode()).element());

          if (from == null || to == null) {
            throw new FlightException("Error at line " + toker.lineno() + ": " +
                                      "airport " + spec.originCode() + " or " +
                                      spec.destinationCode() + " does not exist.");
          }

          g.insertDirectedEdge(from, to, spec);

          Parser.skipLeadingNewlines(toker);
        }
      }
      catch(IOException e) {
        throw new FlightException("IO Error at line " + toker.lineno() +
                                  ": " + e.getMessage());
      }

  }

  static public void skipLeadingNewlines(StreamTokenizer t) 
    throws IOException {
      while(t.nextToken() == t.TT_EOL);
      t.pushBack();
  }
 

  static public AirportSpecs parseAirport(StreamTokenizer toker) 
    throws FlightException, IOException {
      
      String code, city;
      int gmtOffset, x, y;
      if(toker.nextToken() != toker.TT_WORD)
        throw new FlightException("Did not find airport code at "
                                  + toker.lineno());
      if(toker.sval.length() != 3)
        throw new FlightException("Airport code should be 3 letters; Found: "
                                  + toker.sval + " at line " + 
                                  toker.lineno());
      code = toker.sval;

      if(toker.nextToken() != toker.TT_NUMBER)
        throw new FlightException("Did not find GMT offset at line "
                                  + toker.lineno());
      gmtOffset = (int)toker.nval;

      // now convert gmtOffset to minutes from GMT; 
      // hours is the current / 100,
      // minutes is the current % 100
      gmtOffset = (gmtOffset / 100) * 60 + (gmtOffset % 100);

      if(toker.nextToken() != toker.TT_NUMBER)
        throw new FlightException("Did not find airport's x-coordinate at line "
                                  + toker.lineno());
      x = (int)toker.nval;

      if(toker.nextToken() != toker.TT_NUMBER)
        throw new FlightException("Did not find airport's y-coordinate at line "
                                  + toker.lineno());
      y = (int)toker.nval;
      
      city = "";
      while(toker.nextToken() != toker.TT_EOL) {
        city = city + " " + toker.sval;
      }
      return new AirportSpecs(code, city, gmtOffset, x, y);
  } // parseAirport

  
  static public FlightSpecs parseFlight(StreamTokenizer toker, Dictionary airportToVertex) 
    throws IOException, FlightException {

      String airline, orig, dest, plane, fares;
      int flightnum, timeint, depTime, arrTime, gdepTime, garrTime;      

      if(toker.nextToken() != toker.TT_WORD)
        throw new FlightException("Expected flight code at " + 
                                  toker.lineno());
      if(toker.sval.length() > 2) {
        try {
          airline = toker.sval.substring(0, 2);
          flightnum = Integer.parseInt(toker.sval.substring(2));
        }
        catch(NumberFormatException e) {
          throw new FlightException("'" + toker.sval.substring(2) +
                                    "' is not an integer at line " +
                                    toker.lineno());
        }
      } else {
        airline = toker.sval;
        if(toker.nextToken() != toker.TT_NUMBER)
          throw new FlightException("Expected an integer flight number at line" +
                                    toker.lineno());
        flightnum = (int)toker.nval;
      }

      // Parse departure info
      if(toker.nextToken() != toker.TT_WORD)
        throw new FlightException("Expected airport code at line " +
                                  toker.lineno());
      if(toker.sval.length() != 3)
        throw new FlightException("Airport code should be 3 letters; Found: "
                                  + toker.sval + " at line " + 
                                  toker.lineno());
      orig = toker.sval;

      if(toker.nextToken() != toker.TT_NUMBER)
        throw new FlightException("Expected departure time at line " +
                                  toker.lineno());
      timeint = (int)toker.nval;
      if(toker.nextToken() != toker.TT_WORD)
        throw new FlightException("Expected meridian on departure time at line " +
                                  toker.lineno());
      try {
        depTime = StandardOps.parseTime(timeint + toker.sval);
      }
      catch(IllegalArgumentException i) {
        throw new FlightException(i.getMessage() + " at line " +
                                  toker.lineno());
      }

      gdepTime = StandardOps.toGMT
        (depTime,
         ((AirportSpecs)(((Vertex)airportToVertex.find(orig).element()).element())).GMToffset());
      
      // Parse arrival info
      if(toker.nextToken() != toker.TT_WORD)
        throw new FlightException("Expected airport code at line " +
                                  toker.lineno());
      if(toker.sval.length() != 3)
        throw new FlightException("Airport code should be 3 letters; Found: "
                                  + toker.sval + " at line " + 
                                  toker.lineno());
      dest = toker.sval;

      if(toker.nextToken() != toker.TT_NUMBER)
        throw new FlightException("Expected arrival time at line " +
                                  toker.lineno());
      timeint = (int)toker.nval;
      if(toker.nextToken() != toker.TT_WORD)
        throw new FlightException("Expected meridian on arrival time at line " +
                                  toker.lineno());
      try {
        arrTime = StandardOps.parseTime(timeint + toker.sval);
      }
      catch(IllegalArgumentException i) {
        throw new FlightException(i.getMessage() + " at line " +
                                  toker.lineno());
      }
      garrTime = StandardOps.toGMT
        (arrTime,
         ((AirportSpecs)(((Vertex)airportToVertex.find(dest).element()).element())).GMToffset());
      
      
      switch(toker.nextToken()) {
      case TT_WORD:
        plane = toker.sval;
        if(toker.nextToken() == toker.TT_NUMBER)
          plane = plane + (int)toker.nval;
        else toker.pushBack();
        break;
      case TT_NUMBER:
        plane = "" + (int)toker.nval;
        break;
      default:
        throw new FlightException("Expected airplane model type at line " +
                                  toker.lineno());
      }
      fares = "";
      while(toker.nextToken() == toker.TT_WORD) {
        //System.out.println(toker.sval);
        fares = fares + " " + toker.sval;
      }
      if(toker.ttype != toker.TT_NUMBER)
        throw new FlightException("Expected cargo capacity at line " +
                                  toker.lineno());
      int cargo = (int)toker.nval;

      if(toker.nextToken() != toker.TT_EOL)
        throw new FlightException("Expected end of line at line " +
                                  toker.lineno());

      return new FlightSpecs(airline, flightnum, orig, dest,
                             depTime, arrTime, gdepTime, garrTime,
                             plane, fares, cargo);
  }


}
