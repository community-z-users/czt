package net.sourceforge.czt.print.z;

import net.sourceforge.czt.parser.util.Token;

/**
 * A printer that can print Z symbols.
 */
public interface ZPrinter
{

  void printToken(Token token);
}
