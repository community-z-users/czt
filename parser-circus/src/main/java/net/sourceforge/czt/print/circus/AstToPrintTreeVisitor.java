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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.circus.util.CircusString;
import net.sourceforge.czt.parser.circus.CircusToken;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.z.TokenName;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.visitor.*;

/** 
 * AstToPrintTreeVisitors should not use Keyword enum. Instead,
 * they should add the corresponding DecordWord. Thast is becsause
 * the Unicode2Latex parser does not yet know about keywords. 
 * The CircusPrintVisitor.visitPrintParagraph (in ZPrintVisitor) 
 * will associate CircusString as a DecorWord!
 */
public class AstToPrintTreeVisitor
  extends net.sourceforge.czt.print.z.AstToPrintTreeVisitor
  implements BasicProcessVisitor<Term>, ActionParaVisitor<Term>, ProcessParaVisitor<Term>

{
  /**
   * Creates a new ast to print tree visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public AstToPrintTreeVisitor(SectionInfo sectInfo, WarningManager wm)
  {
    super(sectInfo, wm);
  }  
  
  protected WarningManager getWM() {
      return (WarningManager)warningManager_;
  }
  
  private boolean processedState_ = false;
  
  public Term visitProcessPara(ProcessPara term) {     
    // TODO: Check here when we have unboxed versions.
    List list = new ArrayList();
    
    list.add(TokenName.ZED);
    list.add(CircusString.CIRCPROC);    
    
    // TODO: CHECK WITH PETRA HOW TO HANDLE THOSE HERE.
    //       i.e. SHALL WE HAVE printGenFormals as in ZPrintVisitor?
    list.add(visit(term.getGenFormals()));
    list.add(visit(term.getName()));
    list.add(CircusString.CIRCDEF);
    boolean isBasicProcess = (term.getCircusProcess() instanceof BasicProcess);
    
    // basic processes will be spread across different environments
    if (isBasicProcess) {        
        list.add(CircusString.CIRCBEGIN);
        list.add(TokenName.END);
        //NOTE: NL cannot happen after END as a Token!
        //      if needed use it as String/Text like CRLF or \n
        //list.add(TokenName.NL);        
    }
    // adding a printParagraph to the list will make it be print. ok.
    list.add(visit(term.getCircusProcess()));    

    // close the environment for either CIRCEND (basic) or normal processes.
    list.add(TokenName.END);
    return getZPrintFactory().createPrintParagraph(list);
  }
  
  public Term visitActionPara(ActionPara term) {
      List list = new ArrayList();
      list.add(CircusToken.CIRCUSACTION);
      if (CircusUtils.isCircusState(term)) {
        if (processedState_) {
            getWM().warnDuplicatedState(term);
        } else {
            assert CircusUtils.isOnTheFly(term) : "Action para marked as basic process state but not as on-the-fly. PARSER-BUG";
            list.add(CircusString.CIRCSTATE);
            processedState_ = true;
            list.add(visit(term));
        }
      } else { 
          list.add(visit(term.getName()));
          list.add(CircusString.CIRCDEF);
          list.add(visit(term.getCircusAction()));
      }      
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
        getWM().warnMissingFor("process state", term);
    }
    
    // locally declared paragraph within basic process
    for (Iterator<Para> iter = term.getZLocalPara().iterator();
           iter.hasNext();) {
        Para next = iter.next();
        
        // local para cannot be on-the-fly
        if (CircusUtils.isOnTheFly(next)) {
            getWM().warnLocalOnTheFly(next, term);
        } else if (CircusUtils.isCircusState(next)) {
            // if it is state, it can only appear once
            if (processedState_) {
                getWM().warnDuplicatedState(next);
            } else {
                // is must be an horizontal definition, as in name == sch-expr
                // see Parser.xml circusProcessState production for details
                assert ZUtils.isHorizontalSchema(next) : "Inconsistent CircusStateAnn for basic process paragrph " + next;
                processedState_ = true;
                
                // since it is an horizontal schema, we must add a circus environment for it
                list.add(CircusToken.CIRCUSACTION);
                list.add(CircusString.CIRCSTATE);
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
            getWM().warnBadParagraphFor("Implicitly", next, term);
        }
    }
    
    if (term.getMainAction() != null) {
        list.add(CircusToken.CIRCUSACTION);
        list.add(new Decorword(ZString.SPOT));
        list.add(visit(term.getMainAction()));
        list.add(TokenName.NL);
    } else {
        getWM().warnMissingFor("main action", term);
    }
    
    if (hasState && !processedState_) {
        getWM().warnMissingFor("locally or implicitly declared process state", term);
    }        
    
    list.add(TokenName.ZED);
    list.add(CircusString.CIRCEND);
    // the environment closure is done at ProcessPara above
        
    return getZPrintFactory().createPrintParagraph(list);
  }
}
