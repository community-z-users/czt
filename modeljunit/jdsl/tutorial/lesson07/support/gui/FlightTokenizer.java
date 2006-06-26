package support.gui;

/**
 * Tokenizer to read a flight decsription.
 *
 * @version JDSL 2
 */
import java.io.*;
import support.*;

class FlightTokenizer extends StreamTokenizer {
  
  protected FlightTokenizer(Reader r) {
    super(r);
    commentChar('#');
    wordChars('@', '@');
    eolIsSignificant(true);
    lowerCaseMode(false);
    parseNumbers();
  }
}
