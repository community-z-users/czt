/*
  Copyright (C) 2005, 2006 Petra Malik
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

package net.sourceforge.czt.rules.ast;

import java.io.StringWriter;
import java.util.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.impl.CalculateProvisoImpl;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * <p>A CalculateProviso used by the prover.</p>
 *
 * @author Petra Malik
 * @czt.todo Handle bindings!  Probably needs undo.
 */
public class ProverCalculateProviso
  extends CalculateProvisoImpl
  implements ProverProviso
{
  private Status status_ = Status.UNCHECKED;
  private Set<Binding> bindings_;

  public Set<Binding> getBindings()
  {
    return bindings_;
  }

  public void check(SectionManager manager, String section)
  {
    Factory factory = new Factory();
    final Expr expr = getRightExpr();
    if (expr instanceof DecorExpr) 
      checkDecorExpr((DecorExpr)expr, manager, section);
    else if (expr instanceof ApplExpr) {
      ApplExpr applExpr = (ApplExpr) expr;
      Expr left = applExpr.getLeftExpr();
      if ( ! (left instanceof RefExpr)) {
        final String message = left.getClass() +
        " not supported as left exprssion" +
        " of ApplExpr by calculate proviso";
        throw new CztException(message);
      }
      RefExpr refExpr = (RefExpr) left;
      Name refName = refExpr.getName();
      if ( ! (refName instanceof ZName)) {
        final String message = refName.getClass() +
        " is not a supported Name " +
        " for the calculate proviso";
        throw new CztException(message);
      }
      ZName zName = (ZName) refName;
      if (zName.getZStrokeList().size() != 0) {
        final String message = zName +
        " with decorations is not a supported Name " +
        " for the calculate proviso";
        throw new CztException(message);
      }
      String funcName = zName.getWord();
      Expr arg = applExpr.getRightExpr();
      if ("binding".equals(funcName))
        checkBinding(arg, factory);
      else if (funcName.equals(ZString.ARG_TOK+"schemaminus"+ZString.ARG_TOK))
        checkSchemaMinus(arg, factory);
      else if ("print".equals(funcName))
        checkPrint(arg, manager, section);
      else if (funcName.equals(ZString.ARG_TOK+"unprefix"+ZString.ARG_TOK))
        checkUnprefix(arg, factory);
      else
      {
        final String message = funcName +
        " is not supported by the calculate proviso";
        throw new CztException(message);
      }
    }
    else {
      final String message =
        expr.getClass() + " not supported in calculate proviso";
      throw new CztException(message);
    }
  }

  private void checkPrint(Expr expr,
                          SectionManager manager, String section)
  {
    try {
      Term term = ProverUtils.removeJoker(expr);
      StringWriter writer = new StringWriter();
      PrintUtils.print(term, writer, manager, section, Markup.LATEX);
      writer.close();
      System.out.println(writer.toString());
      unify(expr, getLeftExpr());
    }
    catch(ProverUtils.UnboundJokerException e) {
      final String message =
        "Found unbound joker when checking calculate proviso";
      System.err.println(message + "\nCause by:\n  " + e.getMessage());
      status_ = Status.UNKNOWN;
    }
    catch(java.io.IOException e) {
      e.printStackTrace();
      status_ = Status.UNKNOWN;
    }
  }
  
  /** Implements the 'decorated expression' proviso.
   *  For example, given [D] ', this will create a primed
   *  version of [D] and bind it to getLeftExpr().
   *  Every path through this method should set status_.
   */
  private void checkDecorExpr(DecorExpr decorExpr, 
			      SectionManager manager, String section)
  {
    final Stroke stroke = decorExpr.getStroke();
    if (decorExpr.getExpr() instanceof SchExpr) {
      final CollectStateVariablesVisitor collectVisitor =
        new CollectStateVariablesVisitor();
      final DecorateNamesVisitor visitor =
        new DecorateNamesVisitor(collectVisitor.getVariables(), stroke);
      try {
        SchExpr result =
          (SchExpr) ProverUtils.removeJoker(decorExpr.getExpr());
        List errors =
          TypeCheckUtils.typecheck(result, manager, false, true, section);
        if (errors == null || errors.isEmpty()) {
          result.getZSchText().getDeclList().accept(collectVisitor);
          result = (SchExpr) result.accept(visitor);
          if (result != null) {
            unify(result, getLeftExpr());
	    // unify sets status_
          }
	  else {
	      status_ = Status.UNKNOWN; // TODO: should this be FAIL?
	  }
        }
        else {
	  System.err.println("Typeckecking failed:");
	  System.err.println(errors);
	  status_ = Status.FAIL;
        }
      }
      catch(ProverUtils.UnboundJokerException e) {
        final String message =
          "Found unbound joker when checking calculate proviso";
        System.err.println(message + "\nCause by:\n  " + e.getMessage());
	status_ = Status.UNKNOWN;
      }
      catch(CztException e) {
        final String message =
          "Caught CztException when checking calculate proviso";
        System.err.println(message + "\nCause by:\n  " + e.getMessage());
	status_ = Status.UNKNOWN;
      }
    }
  }
  
  /** Implements the 'binding [D]' proviso.
   *  This constructs a binding from the names in D.
   *  For example, if D=[x,y:\num], then getLeftExpr() will
   *  be unified with the binding \lblot x==x, y==y \rblot.
   *  Every path through this method should set status_. 
   */
  private void checkBinding(Expr rightExpr, Factory factory)
  {
    GetZName findName = new GetZName();
    if (rightExpr instanceof SchExpr) {
      SchExpr schExpr = (SchExpr) rightExpr;
      SchText schText = schExpr.getSchText();
      if (schText instanceof ZSchText) {
        ZSchText zSchText = (ZSchText) schText;
        ZDeclList zDeclList =
          zSchText.accept(new GetZDeclList(factory));
        ZDeclList newZDeclList = factory.createZDeclList();
        for (Decl decl : zDeclList) {
          if (decl instanceof VarDecl) {
            VarDecl varDecl = (VarDecl) decl;
            for (Name declName : varDecl.getName()) {
              ZName zName = declName.accept(findName);
              RefExpr newRefExpr = factory.createRefExpr(zName);
              ConstDecl constDecl = factory.createConstDecl(zName,
                                                            newRefExpr);
              newZDeclList.add(constDecl);
            }
          }
          else {
            final String message = decl.getClass() +
            " is not a supported Decl " +
            " for the calculate proviso";
            throw new CztException(message);
          }
        }
        BindExpr bindExpr = factory.createBindExpr(newZDeclList);
        unify(bindExpr, getLeftExpr());
	// unify sets status_
      }
      else {
        final String message = schText.getClass() +
        " is not a supported SchText " +
        " for the calculate proviso";
        throw new CztException(message);
      }
    }
    else {
      final String message = rightExpr.getClass() +
      " is not supported by the binding function " +
      "of the calculate proviso";
      throw new CztException(message);
    }
  }
  
  /** Implements the [D1|true] schemaminus [D2|true] proviso.
   *  This calculates the signature D1 minus D2.
   *  Every path through this method should set status_. 
   * @param args
   */
  private void checkSchemaMinus(Expr args, Factory factory)
  {
    try {
      String op = "\\schemaminus";
      ZExprList argList = null;
      if ( ! (args instanceof TupleExpr)
           || (argList=((TupleExpr)args).getZExprList()).size() != 2)
        throw new CztException(op+" requires two arguments.");
      ZDeclList decls1 = getDeclsFromSchema(op, argList.get(0));
      ZDeclList decls2 = getDeclsFromSchema(op, argList.get(1));
      // create a map of the names in decls2.
      Map<String,Expr> map2 = new HashMap<String,Expr>();
      for (Decl decl : decls2)
      {
        VarDecl vdecl = (VarDecl)decl;
        String name = vdecl.getName().get(0).accept(new PrintVisitor());
        //      System.out.println("map2["+name+"] := "+vdecl.getExpr());
        map2.put(name,vdecl.getExpr());
      }
      // now go through decls1, and filter out any names in map2
      ZDeclList result = factory.createZDeclList();
      for (Decl decl : decls1)
      {
        VarDecl vdecl = (VarDecl)decl;
        String name = vdecl.getName().get(0).accept(new PrintVisitor());
        //      System.out.println("checking name:"+name+".");
        if (map2.containsKey(name)) {
          assert map2.get(name).equals(vdecl.getExpr());
        }
        else {
          //        System.out.println("added name:"+name+".");
          result.add(decl);
      }
      }
      ZSchText schtext = factory.createZSchText(result, factory.createTruePred()); 
      unify(factory.createSchExpr(schtext), getLeftExpr());
      // unify sets status_
    }
    catch (ProverUtils.UnboundJokerException e) {
      status_ = Status.UNKNOWN;
    }
  }

  /** Gets the declarations out of a schema expression, with
   *  a few checks to see if schema is in normal form.
   */
  private ZDeclList getDeclsFromSchema(String op, Expr expr)
    throws ProverUtils.UnboundJokerException
  {
    if ( ! (expr instanceof SchExpr))
      throw new CztException(op+" arguments must be schemas");
    ZSchText text = ((SchExpr)expr).getZSchText();
    if ( ! (text.getPred() instanceof TruePred))
      throw new CztException(op+" arguments should have predicate part = true");
    ZDeclList decls = (ZDeclList) ProverUtils.removeJoker(text.getDeclList());
    for (Decl decl : decls)
    {
      if ( ! (decl instanceof VarDecl))
        throw new CztException(op+" arguments must contain only VarDecls");
      VarDecl vdecl = (VarDecl)decl;
      if (vdecl.getName().size() != 1)
        throw new CztException(op+" arguments must be in normal form");
    }
    return decls;
  }

  private void unify(Term term1, Term term2)
  {
    bindings_ = UnificationUtils.unify(term1, term2);
    if (bindings_ != null) {
      status_ = Status.PASS;
    }
    else {
      status_ = Status.FAIL;
    }
  }

  private void unify2(Term term1, Term term2)
    throws UnificationException
  {
    try {
      bindings_ = UnificationUtils.unify2(term1, term2);
      if (bindings_ != null) {
        status_ = Status.PASS;
      }
      else {
        status_ = Status.FAIL;
      }
    }
    catch(UnificationException e) {
      String message = "ProverCalculateProviso";
      throw new UnificationException(term1, term2, message, e);
    }
  }

  private void checkUnprefix(Expr args, Factory factory)
  {
    status_ = Status.FAIL;
    try {
      args = (Expr) ProverUtils.removeJoker(args);
    }
    catch(ProverUtils.UnboundJokerException e) {
      final String message =
        "Found unbound joker when checking calculate proviso";
      System.err.println(message + "\nCause by:\n  " + e.getMessage());
      status_ = Status.UNKNOWN;
    }
    ZExprList argList = null;
    if ( ! (args instanceof TupleExpr)
         || (argList=((TupleExpr)args).getZExprList()).size() != 2)
      throw new CztException("unprefix requires two arguments.");
    final Expr leftExpr = argList.get(0);
    final Expr rightExpr = argList.get(1);
    if (leftExpr instanceof RefExpr && rightExpr instanceof RefExpr) {
      final ZName leftName = ((RefExpr) leftExpr).getZName();
      final ZName rightName = ((RefExpr) rightExpr).getZName();
      final String leftWord = leftName.getWord();
      final String rightWord = rightName.getWord();
      if (rightWord.startsWith(leftWord)) {
        final String resultWord =
          rightWord.substring(leftWord.length(), rightWord.length());
        StrokeList strokes = rightName.getStrokeList();
        // TODO: clean this up.
        final ZName resultName =
          factory.createZName(resultWord, strokes, "global_i_hope");
        final RefExpr result =
          factory.createRefExpr(resultName);
        unify(result, getLeftExpr()); // unify sets status_
      }
    }
    else {
      final String message = rightExpr.getClass() +
      " is not supported by the unprefix function " +
      "of the calculate proviso";
      throw new CztException(message);
    }
  }

  public Status getStatus()
  {
    return status_;
  }

  public static class GetZDeclList
    implements TermVisitor<ZDeclList>,
               HeadDeclListVisitor<ZDeclList>,
               JokerDeclListVisitor<ZDeclList>,
               SchExprVisitor<ZDeclList>,
               ZDeclListVisitor<ZDeclList>,
               ZSchTextVisitor<ZDeclList>
  {
    private Factory factory_;

    public GetZDeclList(Factory factory)
    {
      factory_ = factory;
    }

    public ZDeclList visitTerm(Term term)
    {
      final String message = term.getClass() +
        " is not a supported DeclList " +
        " for the calculate proviso";
      throw new CztException(message);
    }

    public ZDeclList visitHeadDeclList(HeadDeclList headDeclList)
    {
      ZDeclList rest = headDeclList.getJokerDeclList().accept(this);
      if (rest != null) {
        ZDeclList result = factory_.createZDeclList();
        result.addAll(headDeclList.getZDeclList());
        result.addAll(rest);
        return result;
      }
      return null;
    }

    public ZDeclList visitSchExpr(SchExpr schExpr)
    {
      return schExpr.getSchText().accept(this);
    }

    public ZDeclList visitZSchText(ZSchText zSchText)
    {
      return zSchText.getDeclList().accept(this);
    }

    public ZDeclList visitJokerDeclList(JokerDeclList jokerDeclList)
    {
      if (jokerDeclList instanceof ProverJokerDeclList) {
        Joker joker = (Joker) jokerDeclList;
        Term boundTo = joker.boundTo();
        if (boundTo != null) return boundTo.accept(this);
      }
      final String message = jokerDeclList.getClass() +
        " is not a supported JokerDeclList " +
        " for the calculate proviso";
      throw new CztException(message);
    }

    public ZDeclList visitZDeclList(ZDeclList zDeclList)
    {
      return zDeclList;
    }
  }

  public static class GetZName
    implements TermVisitor<ZName>,
               JokerNameVisitor<ZName>,
               ZNameVisitor<ZName>
  {
    public ZName visitTerm(Term term)
    {
      final String message = term.getClass() +
        " is not a supported Name " +
        " for the calculate proviso";
      throw new CztException(message);
    }

    public ZName visitJokerName(JokerName jokerName)
    {
      if (jokerName instanceof ProverJokerName) {
        Joker joker = (Joker) jokerName;
        Term boundTo = joker.boundTo();
        if (boundTo != null) return boundTo.accept(this);
      }
      final String message = jokerName.getClass() +
        " is not a supported JokerName " +
        " for the calculate proviso";
      throw new CztException(message);
    }

    public ZName visitZName(ZName zName)
    {
      return zName;
    }
  }

  public static class CollectStateVariablesVisitor
    implements ConstDeclVisitor,
               HeadDeclListVisitor,
               InclDeclVisitor,
               VarDeclVisitor,
               JokerDeclListVisitor,
               ZDeclListVisitor
  {
    private Set<Name> variables_ = new HashSet<Name>();

    public Set<Name> getVariables()
    {
      return variables_;
    }

    public Object visitHeadDeclList(HeadDeclList headDeclList)
    {
      for (Decl decl : headDeclList.getZDeclList()) {
        decl.accept(this);
      }
      headDeclList.getJokerDeclList().accept(this);
      return null;
    }

    public Term visitInclDecl(InclDecl inclDecl)
    {
      String message = "CalculateProviso: Schema not normalised";
      throw new IllegalStateException(message);
    }

    public Object visitVarDecl(VarDecl varDecl)
    {
      for (Name declName : varDecl.getName()) {
        variables_.add(declName);
      }
      return null;
    }

    public Object visitConstDecl(ConstDecl constDecl)
    {
      variables_.add(constDecl.getName());
      return null;
    }

    public Object visitJokerDeclList(JokerDeclList jokerDeclList)
    {
      if (jokerDeclList instanceof Joker) {
        Joker joker = (Joker) jokerDeclList;
        Term boundTo = joker.boundTo();
        if (boundTo != null) {
          return boundTo.accept(this);
        }
      }
      throw new CztException("Found unbound Joker");
    }

    public Object visitZDeclList(ZDeclList zDeclList)
    {
      for (Decl decl : zDeclList) {
        decl.accept(this);
      }
      return null;
    }
  }

  public static class DecorateNamesVisitor
    implements InclDeclVisitor<Term>,
               TermVisitor<Term>,
               ZNameVisitor<Term>
  {
    private Set<Name> declNames_;
    private Factory factory_ = new Factory(new ProverFactory());

    /**
     * The stroke to be added to names.
     */
    private Stroke stroke_;

    public DecorateNamesVisitor(Set<Name> declNames, Stroke stroke)
    {
      declNames_ = declNames;
      stroke_ = stroke;
    }

    public Term visitInclDecl(InclDecl inclDecl)
    {
      // TODO: visit children?
      DecorExpr decorExpr =
        factory_.createDecorExpr(inclDecl.getExpr(), stroke_);
      InclDecl result = (InclDecl) inclDecl.create(new Object[] { decorExpr });
      return result;
    }

    public Term visitTerm(Term term)
    {
      if (term instanceof Joker) {
        Joker joker = (Joker) term;
        Term boundTo = joker.boundTo();
        if (boundTo != null) {
          return boundTo.accept(this);
        }
        throw new CztException("Found unbound Joker");
      }
      return (Term) VisitorUtils.visitTerm(this, term, true);
    }

    public Term visitZName(ZName zName)
    {
      Object[] children = zName.getChildren();
      for (int i = 0; i < children.length; i++) {
        if (children[i] instanceof Term) {
          children[i] = ((Term) children[i]).accept(this);
        }
      }
      ZName newName = (ZName) zName.create(children);
      if (declNames_.contains(zName)) {
	ZStrokeList strokes = factory_.createZStrokeList();
	strokes.addAll(newName.getZStrokeList());
	strokes.add(stroke_);
        newName.setStrokeList(strokes);
      }
      return newName;
    }
  }
}
