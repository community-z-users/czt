package support.gui;

/**
 * Tokenizer to read an airport description.
 *
 * @version JDSL 2
 */

import java.io.*;
import support.*;

class AirportTokenizer extends StreamTokenizer {
  
  protected AirportTokenizer(Reader r) {
    super(r);
    commentChar('#');
    wordChars(',', ',');
    wordChars('(', '(');
    wordChars('/', '/');
    wordChars(')', ')');
    wordChars('.', '.');
    eolIsSignificant(true);
    lowerCaseMode(false);
    parseNumbers();
  }
}
