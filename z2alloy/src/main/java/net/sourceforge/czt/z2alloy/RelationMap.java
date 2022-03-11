package net.sourceforge.czt.z2alloy;

import java.util.HashMap;
import java.util.Map;

import static net.sourceforge.czt.z2alloy.ast.Sig.SIGINT;

import net.sourceforge.czt.z2alloy.ast.AlloyExpr;
import net.sourceforge.czt.z2alloy.ast.Field;
import net.sourceforge.czt.z2alloy.ast.Module;
import net.sourceforge.czt.z2alloy.ast.PrimSig;
import net.sourceforge.czt.z2alloy.ast.Sig;
import net.sourceforge.czt.z2alloy.ast.SubsetSig;

public class RelationMap {

  private Map<String, Sig> relations;
  private Module m;

  public RelationMap(Module m) {
    this.relations = new HashMap<String, Sig>();
    this.m = m;
  }

  public boolean contains(AlloyExpr e) {
    return relations.containsValue(e);
  }

  public Sig create(AlloyExpr left, AlloyExpr right) {
    new RuntimeException().printStackTrace();
    String name = left.toString() + "_" + right.toString();
    if (! relations.containsKey(name)) {
      if (right instanceof PrimSig) {
        createBasic(left, right);
      }
      else {
        Sig relation = createRelation(left, right, name);
        relation.addPred(relation.fields().get(0).in(left.product(right)));
      }
    }
    return relations.get(name);

  }

  public Sig createSeq(AlloyExpr body) {
    String name = "Seq_" + body.toString();
    if (! relations.containsKey(name)) {
      Sig relation = createRelation(SIGINT, body, name);
      relation.addPred(relation.fields().get(0).in(body.seq()));
    }
    return relations.get(name);
  }

  public Sig createPFun(AlloyExpr left, AlloyExpr right) {
    String name = left.toString() + "_" + "LONE" + "_" + right.toString();
    if (! relations.containsKey(name)) {
      Sig relation = createRelation(left, right, name);
      relation.addPred(relation.fields().get(0).in(left.any_arrow_lone(right)));
    }
    return relations.get(name);
  }

  private Sig createRelation(AlloyExpr left, AlloyExpr right, String name) {
    if (right instanceof SubsetSig && relations.get(((SubsetSig) right).label()) == right) {
      right = ((SubsetSig) right).parent();
    }
    Sig baseRelation = createBasic(left, right);
    Sig relation = new SubsetSig(name, baseRelation);
    m.addSig(relation);
    relations.put(name, relation);
    return relation;
  }

  private Sig createBasic(AlloyExpr left, AlloyExpr right) {
    if (! (left instanceof PrimSig && right instanceof PrimSig)) {
      //		throw new RuntimeException("left and right must be primsigs left: " + left + " right: " + right);
    }
    String name = left.toString() + "_" + right.toString();
    Sig relation = new PrimSig(name);
    relation.addField(new Field(name.toLowerCase(), left.product(right)));
    m.addSig(relation);
    relations.put(name, relation);
    return relation;
  }

  public Sig retrieve(AlloyExpr left, AlloyExpr right) {
    String name = left.toString() + "_" + right.toString();
    if (relations.get(name) == null) {
      create(left, right);
    }
    return relations.get(name);
  }

}
