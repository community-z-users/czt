/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.z.transformer.refinement;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.vcg.z.refinement.util.ZRefinementKind;
import net.sourceforge.czt.vcg.z.transformer.feasibility.ZPredTransformerFSB;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.util.Factory;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class ZPredTransformerRef extends ZPredTransformerFSB
{
  /**
   * 
   * @param factory
   * @param termV
   */
  public ZPredTransformerRef(Factory factory, Visitor<Pred> termV)
  {
    super(factory, termV);
  }

  public Pred createInitialisationVC(ZRefinementKind kind, Expr absStInit, Expr conStInit, Expr retrieveDash)
  {
    Pred result;
    switch (kind)
    {
      case FORWARD:
        // original: \forall CSInit @ \exists AState' | R' @ ASInit
        // reduced : \forall CSInit @ \exists R' @ ASInit
        result = asPred(factory_.createForallExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(conStInit))),
                  truePred()),
                factory_.createExistsExpr(
                  factory_.createZSchText(
                    factory_.createZDeclList(
                      factory_.list(factory_.createInclDecl(retrieveDash))),
                    truePred()),
                  absStInit)));
        // TODO: \forall CSInit @ \exists AInitIn @ RIn
        break;
      case BACKWARD:
        // original: \forall CSInit | R' @ ASInit
        // with sig: \forall CSInit; Retr~' @ ASInit 
        result = asPred(factory_.createForallExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(conStInit),
                                  factory_.createInclDecl(retrieveDash))),
                  truePred()),
                absStInit));
        // TODO: \forall CSInit | RIn @ AInitIn
        break;
      default:
        throw new AssertionError();
    }
    return result;
  }

  public Pred createInitialisationInputVC(ZRefinementKind kind, Expr absInitIn, Expr conInitIn, Expr retrieveIn)
  {
    Pred result;
    switch (kind)
    {
      case FORWARD:
        // original: \forall CInitIn @ \exists a? : AI @ AInitIn \land RIn
        // reduces : \forall CInitIn @ \exists AInitIn @ RIn
        result = asPred(factory_.createForallExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(conInitIn))),
                  truePred()),
                factory_.createExistsExpr(
                  factory_.createZSchText(
                    factory_.createZDeclList(
                      factory_.list(factory_.createInclDecl(absInitIn))),
                    truePred()),
                  retrieveIn)));
        break;
      case BACKWARD:
        // original: \forall CInitIn; RIn @ AInitIn
        result = asPred(factory_.createForallExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(conInitIn),
                                  factory_.createInclDecl(retrieveIn))),
                  truePred()),
                absInitIn));
        break;
      default:
        throw new AssertionError();
    }
    return result;
  }

    public Pred createFinalisationVC(ZRefinementKind kind, Expr absStFin, Expr conStFin, Expr retrieve)
  {
    Pred result;
    switch (kind)
    {
      case FORWARD:
        // \forall CFinState; R @ AFinState
        result = asPred(factory_.createForallExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(conStFin),
                                  factory_.createInclDecl(retrieve))),
                  truePred()),
                absStFin));

        // TODO: \forall ROut; CFinOut @ AFinOut
        break;
      case BACKWARD:
        // original: \forall CFinState @ \exists A | R @ AFinState
        // reduced : \forall CFinState @ \exists R @ AFinState
        result = asPred(factory_.createForallExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(conStFin))),
                  truePred()),
                factory_.createExistsExpr(
                  factory_.createZSchText(
                    factory_.createZDeclList(
                      factory_.list(factory_.createInclDecl(retrieve))),
                    truePred()),
                  absStFin)));
        // TODO: \forall CFinOut @ \exists ROut @ AFinOut
        break;
      default:
        throw new AssertionError();
    }
    return result;
  }


  public Pred createFinalisationOutputVC(ZRefinementKind kind, Expr absFinOut, Expr conFinOut, Expr retrieveOut)
  {
    Pred result;
    switch (kind)
    {
      case FORWARD:
        // original: \forall ROut; CFinOut @ AFinOut
        result = asPred(factory_.createForallExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(conFinOut),
                                  factory_.createInclDecl(retrieveOut))),
                  truePred()),
                absFinOut));
        break;
      case BACKWARD:
        // original: \forall CFinOut @ \exists a! : AO @ ROut \land AFinOut
        // reduced : \forall CFinOut @ \exists AFinOut @ ROut
        result = asPred(factory_.createForallExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(conFinOut))),
                  truePred()),
                factory_.createExistsExpr(
                  factory_.createZSchText(
                    factory_.createZDeclList(
                      factory_.list(factory_.createInclDecl(absFinOut))),
                    truePred()),
                  retrieveOut)));
        break;
      default:
        throw new AssertionError();
    }
    return result;
  }
          

  /**
   * Creates the feasibility VC predicate for refinement. Various expressions involved
   * include the user-defined OpSig schema. Obviously, if the user cheats, the VC is pointless.
   * It's up to top-layers to enforce that such thing doesn't happen. For instance, the Z Eclipse
   * VCG enforces that the OpSig declarations cannot change, hence rules out having after state
   * in the precondition assumptions.
   * 
   * @param kind
   * @param absOpSig
   * @param absOp
   * @param conOpSig
   * @param conOp
   * @param retrieve
   * @param retrieveInputs
   * @return
   */
  public Pred createFeasibilityVC(ZRefinementKind kind, Expr absOpSig, Expr absOp,
          Expr conOpSig, Expr conOp, Expr retrieve, Expr retrieveInputs)
  {
    Pred result;
    // notice that only the top-level Pred is an ExprPred. All else is a XXXExpr (e.g., AndExpr, ForallExpr, etc)
    switch (kind)
    {
      case FORWARD:
        if (retrieveInputs == null)
          // original: \forall AState; CState | \pre AOp \land Retrieve @ \pre COp
          // with sig: \forall AOpSig; COpSig; Retrieve | \pre~AOp @ \pre~COp
          result = asPred(factory_.createForallExpr(
              factory_.createZSchText(
                factory_.createZDeclList(
                  factory_.list(factory_.createInclDecl(absOpSig),
                                factory_.createInclDecl(conOpSig),
                                factory_.createInclDecl(retrieve))),
                //asPred(factory_.createAndExpr(factory_.createPreExpr(absOp), retrieve)),
                prePred(absOp)),
                factory_.createPreExpr(conOp)));
        else
          // TODO: should this be "AState" instead of AOpSig?
          // with inputs original: \forall R; RIn | \pre AOp @ \pre COp
          // with inputs with sig: \forall AOpSig; COpSig; RIn; Retrieve | \pre~AOp @ \pre~COp
          result = asPred(factory_.createForallExpr(
              factory_.createZSchText(
                factory_.createZDeclList(
                  factory_.list(factory_.createInclDecl(absOpSig),
                                factory_.createInclDecl(conOpSig),
                                factory_.createInclDecl(retrieveInputs),
                                factory_.createInclDecl(retrieve))),
                prePred(factory_.createPreExpr(absOp))),
                factory_.createPreExpr(conOp)));
        break;
      case BACKWARD:
        if (retrieveInputs == null)
          // original: \forall C | (\forall AState | Retrieve @ \pre AOp) @ \pre COp
          // with sig: \forall COpSig | (\forall AOpSig | Retrieve @ \pre AOp) @ \pre COp
          result = asPred(factory_.createForallExpr(
              factory_.createZSchText(
                factory_.createZDeclList(
                  factory_.list(factory_.createInclDecl(conOpSig))),
                asPred(factory_.createForallExpr(
                  factory_.createZSchText(
                    factory_.createZDeclList(
                      factory_.list(factory_.createInclDecl(absOpSig))),
                    asPred(retrieve)),
                  factory_.createPreExpr(absOp)))),
              factory_.createPreExpr(conOp)));
        else
          // with inputs original: \forall C; c?:CI | (\forall A; a?: AI | R \land RIn @ \pre AOp) @ \pre COp
          // with inputs with sig: \forall COpSig | (\forall AOpSig; RIn | R @ \pre AOp) @ \pre COp
          result = asPred(factory_.createForallExpr(
              factory_.createZSchText(
                factory_.createZDeclList(
                  factory_.list(factory_.createInclDecl(conOpSig))),
                asPred(factory_.createForallExpr(
                  factory_.createZSchText(
                    factory_.createZDeclList(
                      factory_.list(factory_.createInclDecl(absOpSig),
                                    factory_.createInclDecl(retrieveInputs))),
                    asPred(retrieve)),
                  factory_.createPreExpr(absOp)))),
              factory_.createPreExpr(conOp)));
        break;
      default:
        throw new AssertionError();
    }
    return result;
  }

  /**
   * The various expressions involved in the VC for refinement. Notice that inputs and outputs
   * are handled at the signatures (e.g., we add COp to quantifiers).
   *
   * @param kind
   * @param absState
   * @param absStateDash
   * @param conState
   * @param absOp
   * @param conOp
   * @param retrieve
   * @param retrieveDash
   * @param retrieveInputs
   * @param retrieveOutputs
   * @return
   */
  public Pred createCorrectnessVC(ZRefinementKind kind, Expr absState, Expr absStateDash,
            Expr absOp, Expr conState, Expr conOp, Expr retrieve, Expr retrieveDash,
            Expr retrieveInputs, Expr retrieveOutputs)
  {
    Pred result;
    switch (kind)
    {
      case FORWARD:
        if (retrieveInputs == null && retrieveOutputs == null)
          // original: (\forall A; C; C' | \pre AOp \land R \land COp @ (\exists A' | R' @ AOp))
          // with sig: (\forall AState; COp; R | \pre AOp @ (\exists A' | R' @ AOp))
          result = asPred(factory_.createForallExpr(
              factory_.createZSchText(
                factory_.createZDeclList(
                  factory_.list(factory_.createInclDecl(absState),
                                factory_.createInclDecl(conOp),
                                factory_.createInclDecl(retrieve))), // have it quantified to have outputs here
                // AndPred chained to the left:  X and Y and Z  =  And(And(X,Y), Z)
                //asPred(factory_.createAndExpr(factory_.createAndExpr(factory_.createPreExpr(absOp), retrieve), conOp))),
                prePred(absOp)),
              factory_.createExistsExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(absStateDash))),
                  asPred(retrieveDash)),
                absOp)));
        else
        {
          assert retrieveInputs != null && retrieveOutputs != null;
          // with io: (\forall AState; COp; R; RIn | \pre AOp @ (\exists AState'; ROut | R' @ AOp))
          result = asPred(factory_.createForallExpr(
              factory_.createZSchText(
                factory_.createZDeclList(
                  factory_.list(factory_.createInclDecl(absState),
                                factory_.createInclDecl(conOp), // have it quantified to have outputs here
                                factory_.createInclDecl(retrieve),
                                factory_.createInclDecl(retrieveInputs))), 
                prePred(absOp)),
              factory_.createExistsExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(absStateDash),
                                  factory_.createInclDecl(retrieveOutputs))),
                  asPred(retrieveDash)),
                absOp)));
        }
        break;
      case BACKWARD:
        if (retrieveInputs == null && retrieveOutputs == null)
          // original: \forall C | (\forall A | R @ \pre AOp) @ (\forall A'; C' | CO \lad R' @ (\exists A @ R \land AOp))
          // with sig: \forall CState | (\forall AState | Retr @ \pre AOp) @ (\forall AState~'; COp | Retr~' @ (\exists AState | Retr @ AOp))
          result = asPred(factory_.createForallExpr(
              factory_.createZSchText(
                factory_.createZDeclList(
                  factory_.list(factory_.createInclDecl(conState))),
                asPred(factory_.createForallExpr(
                  factory_.createZSchText(
                    factory_.createZDeclList(
                      factory_.list(factory_.createInclDecl(absState))),
                    asPred(retrieve)),
                  factory_.createPreExpr(absOp)))),
              factory_.createForallExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(absStateDash),
                                  factory_.createInclDecl(conOp))),
                  asPred(retrieveDash)),
                factory_.createExistsExpr(
                  factory_.createZSchText(
                    factory_.createZDeclList(
                      factory_.list(factory_.createInclDecl(absState))),
                  asPred(retrieve)),
                absOp))));
        else
        {
          assert retrieveInputs != null && retrieveOutputs != null;
          // with io: (\forall C; c?: CI | (\forall A; a?: AI | R \land RIn @ \pre AOp) @ (\forall C'; c!: CO; A'; a!: AO | COp \land R' \land ROut @ (\exists A; a?: AI @ R \land RIn \land AOp)))
          //        = C \land c? \in CI \land (\forall A; a?: AI | R \land RIn @ \pre AOp) \implies (\forall C'; c!: CO; A'; a!: AO | COp \land R' \land ROut @ (\exists A; a?: AI @ R \land RIn \land AOp)))
          //        = C \land c? \in CI \land (\forall A; a?: AI | R \land RIn @ \pre AOp) \land C' \land c! \in CO \land A' \land a! \in AO \land COp \land R' \land ROut \implies (\exists A; a?: AI @ R \land RIn \land AOp)))
          //        = (\forall COp; ROut; R' | (\forall A; RIn | R @ \pre AOp) @ (\exists A; a?: AI @ R \land RIn \land AOp))
          //        = (\forall COp; ROut; R' | (\forall A; RIn | R @ \pre AOp) @ (\exists A; R; RIn @ AOp))

          // with io: (\forall COp; ROut; R' | (\forall A; RIn | R @ \pre AOp) @ (\exists A; R; RIn @ AOp)) - see zrefinesEquivProof.tex in parser-zeves for equivalence proof
          result = asPred(factory_.createForallExpr(
              factory_.createZSchText(
                factory_.createZDeclList(
                  factory_.list(factory_.createInclDecl(conOp),
                                factory_.createInclDecl(retrieveOutputs),
                                factory_.createInclDecl(retrieveDash))),
                asPred(factory_.createForallExpr(
                  factory_.createZSchText(
                    factory_.createZDeclList(
                      factory_.list(factory_.createInclDecl(absState),
                                    factory_.createInclDecl(retrieveInputs))),
                    asPred(retrieve)),
                  factory_.createPreExpr(absOp)))),
              factory_.createExistsExpr(
                factory_.createZSchText(
                  factory_.createZDeclList(
                    factory_.list(factory_.createInclDecl(absState),
                                  factory_.createInclDecl(retrieveInputs))),
                asPred(retrieve)),
              absOp)));
        }
        break;
      default:
        throw new AssertionError();
    }
    return result;
  }
}
