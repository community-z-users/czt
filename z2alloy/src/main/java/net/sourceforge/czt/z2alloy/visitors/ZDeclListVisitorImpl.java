package net.sourceforge.czt.z2alloy.visitors;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z2alloy.Z2Alloy;
import net.sourceforge.czt.z2alloy.ast.ExprVar;

public class ZDeclListVisitorImpl implements ZDeclListVisitor<List<ExprVar>> {

  public List<ExprVar> visitZDeclList(ZDeclList zDeclList) {
    List<ExprVar> list = new ArrayList<ExprVar>();
    for (Decl decl : zDeclList) {
        list.add((ExprVar) Z2Alloy.getInstance().visit(decl));
     }
    return list;
  }

}
