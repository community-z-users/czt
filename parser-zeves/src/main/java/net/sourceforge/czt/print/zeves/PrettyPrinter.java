/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.zeves;

import java.util.Arrays;
import java.util.List;
import java.util.ListIterator;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.parser.zeves.ZEvesProofKeyword;
import net.sourceforge.czt.parser.zeves.ZEvesProofToken;
import net.sourceforge.czt.parser.zeves.ZEvesSymMap;
import net.sourceforge.czt.print.util.TokenSequence;

/**
 *
 * @author Leo
 */
public class PrettyPrinter 
        extends net.sourceforge.czt.print.util.PrettyPrinter
{

  private boolean seenZProof_ = false;
  private static final List<? extends Token>
          ZEVES_HEAD_PROOF_WORDS = Arrays.asList(ZEvesProofKeyword.headProofWordsOnly());

  private static final List<? extends Token>
          ZEVES_USAGE_WORDS = Arrays.asList(ZEvesProofKeyword.usageWordsOnly());

  @Override
  protected int handleSpaces(ListIterator<Token> iter, Token previous, Token current, int spaceLeft, int length, int processed, int indentAmount)
  {
    // if I haven't seen ZPROOF yet, check it
//    if (!seenZProof_)
//    {
//      seenZProof_ = previous.equals(ZEvesProofToken.ZPROOF) ||
//                     current.equals(ZEvesProofToken.ZPROOF);
//    }
//    // if I have seen it, then finish only when current is END
//    else
//    {
//      seenZProof_ = !current.equals(ZToken.END);
//    }

    return super.handleSpaces(iter, previous, current, spaceLeft, length, processed, indentAmount);
  }

  @Override
  protected boolean isSpecialTokenCase(Token previous, Token current)
  {
    return super.isSpecialTokenCase(previous, current)
            ||
           // ZED DISABLED
           (previous.equals(ZToken.ZED) && current.equals(ZEvesProofToken.DISABLEDTHMTAG))
            ||
           // SCH/GENSCH DISABLEDDEFTAG
           ((previous.equals(ZToken.SCH) || previous.equals(ZToken.GENSCH))
            && current.equals(ZEvesProofToken.DISABLEDDEFTAG))
            ||
           // LABEL DISABLED, LABEL RULE, LABEL NAME etc
           (previous.equals(ZEvesProofToken.LLABEL) && 
                (current.equals(ZEvesProofKeyword.DISABLED)
                    ||
                 ZEVES_USAGE_WORDS.contains(current)
                    ||
                 current.getName().equals(ZToken.DECORWORD.getName())
                ))
            ||
           // DISABLED RULE, DISABLE NAME, etc
           (previous.equals(ZEvesProofKeyword.DISABLED) &&
                (ZEVES_USAGE_WORDS.contains(current)
                  ||
                 current.getName().equals(ZToken.DECORWORD.getName())
                ))
            ||
           // RULE NAME, etx
           (ZEVES_USAGE_WORDS.contains(previous) &&
                (current.getName().equals(ZToken.DECORWORD.getName())))
            ||
           // NAME RLABEL
           (previous.getName().equals(ZToken.DECORWORD.getName())
             && current.equals(ZEvesProofToken.RLABEL));
          //||
          // (seenZProof_ && isWithinZProofHeader(previous, current));
  }

  protected boolean isWithinZProofHeader(Token previous, Token current)
  {
    assert seenZProof_;
    if (current instanceof TokenSequence)
    {
      final TokenSequence seq = (TokenSequence) current;
      final List<Token> list = seq.getSequence();
      if (list.isEmpty()) return false;
      return isWithinZProofHeader(previous, list.get(0));
    }
    else if (previous instanceof TokenSequence)
    {
      final TokenSequence seq = (TokenSequence) previous;
      final List<Token> list = seq.getSequence();
      if (list.isEmpty()) return false;
      return isWithinZProofHeader(list.get(list.size()-1), current);
    }
    else
    {
      boolean result = previous.getName().equals(ZToken.DECORWORD.getName()) &&
                       ZEVES_HEAD_PROOF_WORDS.contains(current);
      seenZProof_ = !result;
      return result;
    }
  }

}
