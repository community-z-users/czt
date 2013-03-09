/*
 * CircusParseMessage.java
 *
 * Created on 22 March 2006, 13:53
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.zeves;


public enum ZEvesParseMessage {
  
  MSG_NOT_WITHIN_PROOFSCRIPT("Recognised proof command word _ {0} _ outside zproof environment.", " The lexer is identifying a proof command word from a part of the specification outside a zproof. Try and see if you have any name overlap with any of the possible proof command words"),

  MSG_NOT_WITHIN_AXDEF("Recognised Z/EVES predicate label {0} outside axiomatic box.", "The lexer is identifying a Z/EVES label from a part of the specification where it is not allwoed."),
  MSG_CANNOT_ADD_PROOFSCRIPT ("Cannot add named proof script ({0}). "),
  MSG_CANNOT_MERGE_PROOFTABLES("Cannot merge the parent proof script tables ({0}). "),
  MSG_INVALID_SPECIAL_THM_SUFFIX("Special theorem name suffix {0} cannot have strokes. "),

  MSG_INVALID_AXPARA_ABILITY("Only named abbreviations can have ability within unboxed paragraph {0}."),
  MSG_UNKNOWNPARA_ABILITY("Cannot have ability tag on the unknown unboxed paragraph {0}."),
  MSG_WARNING_VDASH_IN_CONJECTURE("Z/EVES conjectures do not have (the need for) '\\vdash?' symbol: on theorem named {0} at {1}."),
  MSG_WARNING_OPNAME_IN_REFNAME("Cannot use operator name in Z/EVES instantiation or renaming: on name {0} at {1}."),
  MSG_UNBOXED_CONJPARA("Invalid Z/EVES conjectures as unboxed para with '\\vdash?' symbols. Z/EVES conjectures can appear within 'theorem' environments only: on theorem named {0} as {1}."),
  MSG_UMATCHED_SYNDEFOPNAME("Unmatched Z/EVES operator name within operator template class lexing - {0}"),
  
  MSG_UNHANDLED_PROOFWORD("Proof word is to be dealt with by the SmartScanner! - {0}")

  ;

  private final String message_;
  private final String explanation_;
  private boolean flagged_;

  ZEvesParseMessage(String message)
  {
    this(message, null);
  }

  ZEvesParseMessage(String message, String explanation)
  {    
    message_ = message;
    explanation_ = explanation;
    flagged_ = false;
  }

  public String getMessage()
  {
    return message_;
  }

  String getExplanation()
  {
    String result = explanation_;
    flagged_ = true;
    return result;
  }
  
  boolean alreadyFlagged()
  {
    return flagged_;
  }
  
  String getFullMessage()
  {
    String result = getMessage();
    if (!flagged_) result += getExplanation();
    return result;
  }  
}
