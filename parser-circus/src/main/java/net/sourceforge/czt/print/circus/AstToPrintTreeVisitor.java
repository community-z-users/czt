/*
  Copyright (C) 2006 Leo Freitas
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.print.circus;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.parser.circus.CircusKeyword;
import net.sourceforge.czt.parser.circus.CircusToken;
import net.sourceforge.czt.parser.z.Keyword;
import net.sourceforge.czt.parser.z.TokenName;
import net.sourceforge.czt.print.ast.PrintParagraph;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.visitor.*;

public class AstToPrintTreeVisitor
  extends net.sourceforge.czt.print.z.AstToPrintTreeVisitor
  /*implements BasicProcessVisitor<Term>, ActionParaVisitor<Term>*/

{
  /**
   * Creates a new ast to print tree visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public AstToPrintTreeVisitor(SectionInfo sectInfo)
  {
    super(sectInfo);
  }
  /*
  private void warn(CircusPrintMessage cpm, Object... arguments) {
      CztLogger.getLogger(PrintUtils.class).warning(MessageFormat.format(
          cpm.getMessage(), arguments));
  }
  
  private void warnMissingFor(String msg, BasicProcess term) {
      warn(CircusPrintMessage.MSG_BASIC_PROCESS_MISSING_ENTITY, msg, term);
  }
  
  private void warnBadParagraphFor(String msg, Para para, BasicProcess term) {
      warn(CircusPrintMessage.MSG_BASIC_PROCESS_BAD_PARAGRAPH, msg, para, term);      
  }  
  
  private void warnLocalOnTheFly(Term para, BasicProcess term) {      
      warn(CircusPrintMessage.MSG_BASIC_PROCESS_LOCAL_ONTHEFLY_PARAGRAPH, para, term);      
  }
    
  private void warnDuplicatedState(Term term) {      
      warn(CircusPrintMessage.MSG_BASIC_PROCESS_DUPLICATED_STATE_PARAGRAPH, term);      
  }
  
  private boolean processedState_ = false;
  
  public Term visitActionPara(ActionPara term) {
      List list = new ArrayList();
      list.add(CircusToken.CIRCUSACTION);
      if (CircusUtils.isCircusState(term)) {
        if (processedState_) {
            warnDuplicatedState(term);
        } else {
            list.add(CircusKeyword.CIRCSTATE);
            processedState_ = true;
        }
      }
      list.add(visit(term));
      list.add(TokenName.END);
      return getZPrintFactory().createPrintParagraph(list);
  }
  
  public Term visitBasicProcess(BasicProcess term) {
    List list = new ArrayList();    
    
    processedState_ = false;
    boolean hasState = (term.getStatePara() != null);
    
    // basic process state is part of either implicitly declared or local paras
    if (!hasState) {
        // it should not be null if term was created by the parser!
        // thus, raise an warning!
        warnMissingFor("process state", term);
    }
    
    // locally declared paragraph within basic process
    for (Iterator<Para> iter = term.getZLocalPara().iterator();
           iter.hasNext();) {
        Para next = iter.next();
        
        // local para cannot be on-the-fly
        if (CircusUtils.isOnTheFly(next)) {
            warnLocalOnTheFly(next, term);
        } else if (CircusUtils.isCircusState(next)) {
            // if it is state, it can only appear once
            if (processedState_) {
                warnDuplicatedState(next);
            } else {
                // is must be an horizontal definition, as in name == sch-expr
                // see Parser.xml circusProcessState production for details
                assert ZUtils.isHorizontalSchema(next) : "Inconsistent CircusStateAnn for basic process paragrph " + next;
                processedState_ = true;
                
                // since it is an horizontal schema, we must add a circus environment for it
                list.add(CircusToken.CIRCUSACTION);
                list.add(CircusKeyword.CIRCSTATE);
                list.add(visit(next));
                list.add(TokenName.END);
            }
        } else {
            list.add(visit(next));        
        }
        if (iter.hasNext()) list.add(TokenName.NL);
    }
    
    // implicitly declared action paragraphs
    for (Iterator<Para> iter = term.getZOnTheFlyPara().iterator();
           iter.hasNext();) {
        Para next = iter.next();
        if (next instanceof ActionPara) {
            ActionPara ap = (ActionPara)next;
            list.add(visit(next));
            if (iter.hasNext()) list.add(TokenName.NL);
        } else {
            warnBadParagraphFor("Implicitly", next, term);
        }
    }
    
    if (term.getMainAction() != null) {
        list.add(Keyword.SPOT);
        list.add(visit(term.getMainAction()));
    } else {
        warnMissingFor("main action", term);
    }
        
    return getZPrintFactory().createPrintParagraph(list);
  }*/
}
