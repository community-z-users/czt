package net.sourceforge.czt.print.z;

import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.session.Dialect;

/**
 * A printer that can print Z symbols.
 */
public interface ZPrinter
{
  Dialect getDialect();
  void printToken(Token token);
}
