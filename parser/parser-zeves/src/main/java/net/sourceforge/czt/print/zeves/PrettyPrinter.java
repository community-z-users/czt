/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.zeves;

import java.util.Arrays;
import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.parser.zeves.ZEvesProofKeyword;
import net.sourceforge.czt.parser.zeves.ZEvesProofToken;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;

/**
 *
 * @author Leo
 */
public class PrettyPrinter 
        extends net.sourceforge.czt.print.util.PrettyPrinter
{
  //private boolean seenZProof_ = false;
  //private static final List<? extends Token>
  //        ZEVES_HEAD_PROOF_WORDS = Arrays.asList(ZEvesProofKeyword.headProofWordsOnly());

  private static final List<? extends Token>
          ZEVES_USAGE_WORDS = Arrays.asList(ZEvesProofKeyword.usageWordsOnly());

  protected boolean formatProofGoal_;

  public PrettyPrinter(Term term, int initW)
  {
    this(term, initW, term instanceof Pred || term instanceof Expr);
  }

  public PrettyPrinter(Term term, int initW, boolean formatProofG)
  {
    super(term, initW);
    formatProofGoal_ = formatProofG;
  }

  public void setFormatProofGoal(boolean v)
  {
    formatProofGoal_ = v;
  }

  public boolean isFormattingProofGoals()
  {
    return formatProofGoal_;
  }

  @Override
  protected int handleSpaces(ListIterator<Token> iter, Token previous, 
          Token current, int spaceLeft, int length, boolean startedProcessing, int indentAmount)
  	throws PrintException
  {
    return super.handleSpaces(iter, previous, current, spaceLeft, length, startedProcessing, indentAmount);
  }

  @Override
  protected boolean isSpecialTokenCase(Token previous, Token current) throws PrintException
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

  @Override
  protected boolean considerAddingNL(Token previous, Token current,
          int spaceLeft, int length, boolean startedProcessing) throws PrintException 
  {
    return super.considerAddingNL(previous, current, spaceLeft, length, startedProcessing)
            ||
           (formatProofGoal_ &&
           (previous.equals(ZKeyword.AND)
           // ||
           //current.equals(ZKeyword.AND)
            ||
           current.equals(ZKeyword.IMP)
            ||
           previous.equals(ZKeyword.IMP)))
           ;
  }

  @Override
  protected boolean considerAddingNLForToken(Token previous, Token current,
          int spaceLeft, int length, boolean startedProcessing) throws PrintException
  {
    boolean result = super.considerAddingNLForToken(previous, current, spaceLeft, length, startedProcessing); // always false for Z
    result = current.equals(ZKeyword.IF) || current.equals(ZKeyword.ELSE) || current.equals(ZKeyword.THEN);
    return result;
  }
}
