package net.sourceforge.czt.z2alloy.visitors;

import static net.sourceforge.czt.z.util.ZUtils.assertZBranchList;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;
import net.sourceforge.czt.z2alloy.Z2Alloy;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.Enum;

public class FreetypeVisitorImpl extends AbstractVisitor implements
  FreeParaVisitor<AlloyExpr>,
  FreetypeVisitor<AlloyExpr>,
  ZFreetypeListVisitor<AlloyExpr> {

  /*
   * TODO clare: confirm that this just wraps around a free type declaration
   */
  public AlloyExpr visitFreePara(FreePara para) {
    return visitZFreetypeList((ZFreetypeList) para.getFreetypeList());
  }

  public AlloyExpr visitFreetype(Freetype freetype) {
    String parent = Z2Alloy.getInstance().print(freetype.getName());
    Iterator<Branch> i = assertZBranchList(freetype.getBranchList()).iterator();
    List<String> children = new ArrayList<String>();
    while (i.hasNext()) {
      Branch branch = (Branch) i.next();
      if (branch.getExpr() != null)
        System.err.println("free types must be simple enumerations, but "
            + branch.getName() + " branch has expression " + branch.getExpr());
      children.add(Z2Alloy.getInstance().print(branch.getName()));
    }
    Z2Alloy.getInstance().module().addSig(new Enum(parent, children));
    return null;
  }

  /**
   * visits each element of the list
   * 
   * @return null
   */
  public AlloyExpr visitZFreetypeList(ZFreetypeList list) {
    for (Freetype freetype : list) {
      visitFreetype(freetype);
    }
    return null;
  }

}
