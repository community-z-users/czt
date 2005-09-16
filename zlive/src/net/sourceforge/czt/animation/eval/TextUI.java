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
import java.util.logging.*;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.parser.util.ParseException;

public class TextUI {
  private static final Logger sLogger
  = Logger.getLogger("net.sourceforge.czt.animation.eval");
  
  protected static ZLive animator = new ZLive();

  // @czt.todo Provide commands for displaying and changing this.
  protected static Markup markup_ = Markup.LATEX;
  
  public static void main (String args[])
        throws IOException
  {
    BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
    String str;
    System.out.println("\n\nZLive Version 0.1\n2004 Release\n");

    // set up a specific logger with our human-readable format
    Logger logger = Logger.getLogger("net.sourceforge.czt.animation.eval");
    logger.setLevel(Level.FINEST);
    Handler fh = new FileHandler("zlive.log");
    fh.setLevel(Level.ALL);
    fh.setEncoding("utf8");
    fh.setFormatter(new ZFormatter());
    logger.addHandler(fh);
    logger.setUseParentHandlers(false); // just use this handler

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
         System.out.println("\neval <Expression> - Evaluate an expression");
         System.out.println("evalp <Predicate> - Evaluate a predicate");
         System.out.println("why - Print out the optimised code of the last command");
         System.out.println("version - Display the version of ZLive");
         System.out.println("quit - Exit the ZLive program");
       }
       else if (cmd.equals("ver")) {
         System.out.println("\nZLive Version 0.2");
         System.out.println("2005 Release\n");
       } 
       else if (cmd.equals("why")) {
         animator.printCode();
       }
       else if (cmd.equals("evalp")) {
	Source src = new StringSource(args);
	src.setMarkup(markup_);
        Pred pred = ParseUtils.parsePred(src, null,
					 animator.getSectionManager());
        System.out.println("Pred="+pred);
        Pred result = animator.evalPred(pred);
        System.out.println("Result="+result);
       }
       else if (cmd.equals("eval")) {
	Source src = new StringSource(args);
	src.setMarkup(markup_);
        Expr expr = ParseUtils.parseExpr(src, null,
					 animator.getSectionManager());
        System.out.println("Expr="+expr);
        Expr result = animator.evalExpr(expr);
	// TODO: add a proper AST printing method to Unicode or LaTeX.
	if (result instanceof NumExpr) {
	  NumExpr num = (NumExpr) result;
          ZNumeral znum = (ZNumeral) num.getNumeral();
          System.out.println(znum.getValue());
        }
	else
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
}