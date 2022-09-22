package net.sourceforge.czt.z2alloy.visitors;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;

public class ZDeclListVisitorImpl extends AbstractVisitor implements ZDeclListVisitor<List<AlloyExpr>> {

  public List<AlloyExpr> visitZDeclList(ZDeclList zDeclList) {
    List<AlloyExpr> list = new ArrayList<AlloyExpr>();
    for (Decl decl : zDeclList) {
        list.add(visit(decl));
     }
    return list;
  }

}
