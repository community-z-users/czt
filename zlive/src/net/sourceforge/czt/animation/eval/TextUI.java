/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval;

import java.io.*;
import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.util.ParseException;

public class TextUI {
  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval");
  
  protected static ZLive animator = new ZLive();
  
  public static void main (String args[])
        throws IOException
  {
    BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
    String str;
    System.out.println("\n\nZLive Version 0.1\n2004 Release\n");
    boolean finished = false;
    while (!finished) {
      System.out.print("zlive>");
      str = br.readLine();
      if (str == null || str.equals("quit") || str.equals("exit"))
        finished = true;
      else if (!str.equals("")) {
        String parts[] = str.split(" ",2);
        processCmd(parts[0],parts.length > 1 ? parts[1] : "");
      }
    }
  }
  
  /** Process one input command. */
  public static void processCmd(String cmd, String args) {
    try {
       if (cmd.equals("help")) {
         System.out.println("\n         ---- ZLive Help ----");
         System.out.println("\neval <Expression to be evaluated> - To evaluate an expression");
         System.out.println("evalp <Predicate to be checked for truth> - To evaluate a predicate");
         System.out.println("code - To print out the code for the last command");
         System.out.println("ver - To check the version of ZLive");
         System.out.println("exit - To exit the zlive prompt");
       }
       else if (cmd.equals("ver")) {
         System.out.println("\nZLive Version 0.1");
         System.out.println("2004 Release\n");
       } 
       else if (cmd.equals("code")) {
         animator.printCode();
       } 
       else if (cmd.equals("evalp")) {
        Pred pred = parsePred(args);
        System.out.println("Pred="+pred);
        Pred result = animator.evalPred(pred);
        System.out.println("Result="+result);
       }
       else if (cmd.equals("eval")) {
        Expr expr = parseExpr(args);
        System.out.println("Expr="+expr);
        Expr result = animator.evalExpr(expr);
        System.out.println("Result="+result);
      }
      else {
        System.out.println("Invalid command.  Try 'help'?");
      }
    }
    catch (Exception e) {
      System.out.println("Error: " + e);
      e.printStackTrace();
    }
  }
  
  /** Parse a LaTeX string into a Pred object. */
  public static Pred parsePred(String str) 
  throws ParseException, FileNotFoundException {
    sLogger.entering("TextUI","parsePred");
    sLogger.fine("parsing: "+str);
    String specStr = "\\begin{axdef} \\where\n" + str + " \\end{axdef}";
    //System.out.println(cmd + " " + str);
    //System.out.println(specStr);
    Spec spec = (Spec)ParseUtils.parseLatexString(specStr, animator.getSectionManager());
    ZSect sect = (ZSect)spec.getSect().get(0);
    // find first AxPara
    AxPara axPara = null;
    for (Iterator i = sect.getPara().iterator(); i.hasNext(); ) {
      Object p = i.next();
      if (p instanceof AxPara) {
        axPara = (AxPara)p;
        break;
      }
    }
    sLogger.exiting("TextUI","parsePred",axPara.getSchText().getPred());
    return axPara.getSchText().getPred();
  }

  /** Parse a LaTeX string into an Expr object. */
  public static Expr parseExpr(String str) 
  throws ParseException, FileNotFoundException {
    String specStr = "\\begin{axdef} result=="+str+" \\end{axdef}";
    //System.out.println(cmd + " " + str);
    //System.out.println(specStr);
    Spec spec = (Spec)ParseUtils.parseLatexString(specStr, animator.getSectionManager());
    ZSect sect = (ZSect)spec.getSect().get(0);
    // find first AxPara
    AxPara axPara = null;
    for (Iterator i = sect.getPara().iterator(); i.hasNext(); ) {
      Object p = i.next();
      if (p instanceof AxPara) {
        axPara = (AxPara)p;
        break;
      }
    }
    List decls = axPara.getSchText().getDecl();
    ConstDecl constDecl = (ConstDecl)decls.get(0);
    return constDecl.getExpr();
  }
}
