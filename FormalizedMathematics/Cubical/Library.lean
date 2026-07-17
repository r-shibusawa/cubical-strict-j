import FormalizedMathematics.Cubical.LibCircleEM
import FormalizedMathematics.Cubical.LibTower
import FormalizedMathematics.Cubical.LibStrictness
import FormalizedMathematics.Cubical.LibSwitchover

/-! # The cubical object-language library — index and summary

The library is split into a chain of modules (each importing the
previous): LibCore → LibSets → LibGroupoid → LibLoop → LibCats →
LibHedberg → LibHITs → LibQuot → LibWords → LibEM → LibCoherence → LibCircleEM.  This file assembles the
index. -/

namespace Cubical.Library

open Raw

/-! ## Summary -/

def allDefs : List LibDef :=
  [reflD, symmD, transD, congD, happlyD, funExtD,
   transportD, substD, jD,
   contrSinglD, contrToPropD,
   idEquivD, uaD, pathToEquivD,
   sucZD, predZD, predSucZD, sucPredZD, addD, addZeroLD, addZeroRD,
   isPropUnitD, isPropEmptyD,
   codeNatD, rNatD, encodeNatD, decodeNatD, isPropCodeNatD,
   decodeEncodeReflNatD, decodeEncodeNatD, isSetNatD,
   codeZD, rZD, encodeZD, decodeZD, isPropCodeZD,
   decodeEncodeReflZD, decodeEncodeZD, isSetZD,
   setFillD, sucEquivD, helixD, windingD,
   addSucRD, addPredRD, addAssocD, intMonoidD,
   addSucLD, addPredLD, addCommD,
   intLoopD, windingCompLoopD, windingCompLoopInvD, encodeDecodeD,
   decodeSquareD, encodeD, decodeD, decodeEncodeD2, pi1S1IsoIntD,
   loopNeqReflD, s1NotSetD, setIsoToEquivD,
   isPropPi11D, transport1D, toPathP1D, cong11D, compNatD, natTransEqD,
   functorCatD, intDeloopD, endoBZCatD,
   pi1S1EquivD, loopSpaceIsIntD, compFunctorD, whiskerLD, whiskerRD,
   isPropRetractD, isSetRetractD, isSetLoopS1D, transInvRD, transInvLD,
   notBoolD, notNotD, codeBoolD, rBoolD, encodeBoolD, decEqBoolD,
   hedbergD, isSetBoolD, notEquivD,
   interchangeD, decCodeNatD, decEqNatD, decCodeZD, decEqZD, isPropSigmaD,
   toBoolD, fromBoolD, s0SectD, s0RetrD, s0EquivBoolD, s0IsBoolD,
   suspMapD, suspMapIdD, sigmaS1D,
   t2ToS1S1D, s1s1ToT2D, t2SectD, t2RetrD, t2IsoS1S1D,
   isoToEquivD, t2EquivS1S1D, t2IsS1S1D,
   isPropTruncD, truncMapD, truncIdemD, s1ConnectedD, windingSurjD,
   suspToPushD, pushToSuspD, suspPushSectD, suspPushRetrD, suspIsPushoutD,
   figureEightD,
   isSetProdD, sucLeftEquivD, sucRightEquivD, helix8D, wind8D,
   isSetQuotD, isPropPathPSetD, qelimPropD, isPropQuotTotalD, truncAsQuotD,
   addNatD, addZeroRNatD, addSucRNatD, addCommNatD,
   subNatD, subSucSucD, subAddCancelRD,
   nnQuotToZD, zToNNQuotD, predQD, fromPredZD, nnRoundD, zRoundD,
   intAsQuotD,
   decEqProdD, decEqLetterD, lcodeNilD, headDD, tailDD, decEqListD,
   decEqWordD, isSetWordD,
   andBoolD, eqBoolD, isTrueD, isPropIsTrueD, andElimLD, andElimRD,
   andIntroD, notTrueFalseD, eqBoolReflD, eqBoolSoundD, eqBoolFalseD,
   sigmaPropEqD, isSetSigmaPropD,
   invLetD, cancelsD, eqBoolNotLD, cancelsInvD, cancelsCharacD,
   redAuxD, redRelaxD, isSetF2D, consStepD, consGD, consGRoundD,
   invInvLetD, consGEquivD, helixF2D, windF2D,
   isSetToGpdD, em1ZD, emloopD, emloopCompD, pentagonD, triangleD,
   pentagonZD, transFillD, transFillLD, assocConnD,
   transReflRReflD, congSlideD, natReflRD, natReflLD, cancelLD, eckmannHiltonD, triangleConnD,
   pentDiagD, pentDiagLD, pentNatLD, pentNatRD, pentRefillD, pentNatWD,
   pentRefillReflD, pentagonConnD, loopGroupD, loopRecD, loopRecLoopD,
   propToSetD, emConnD, s1ConnD, genLoopD, decodeWordD, decodeF2D,
   fundGpdD, gpdAtD, groupToUnitGpdD, fundGpdLoopD, congTransD, fundGpdMapD, congCompD, gpdMorIdD, gpdMorCompD,
   loop2CommMonoidD, isGpdBGD, barrCompD, barrReflD, barrCongBptD,
   gpdRecD, gpdRecPtD, gpdRecArrD, bgptRetrD, bgFundEquivD, bgFundIsD,
   cancelViaD, conjCancelGenD, gcancelD, decodeConsStepD, decodeConsD,
   cancelRD, intLoopSucD, intLoopPredD,
   intLoopCompD, propFillD,
   negZD, addInvPosD, addInvNegD, addInvRD, addInvLD, zGroupD, emloopOneD,
   isPropIsContrD, isPropIsEquivD, isSetPiD, isSetEquivD,
   j1D, uaIdEquivD, uaEtaD, isSetRetract10D, isSetPathUD,
   isPropIsSetD, sigmaPropEq10D, isPropPathPSet1D, isSetRetract11D, hSetPathD,
   hSetPathEtaD, hSetPathUniqueD, isGroupoidHSetD,
   mulREquivD, equivEqD, uaInjD, isGpdEMD, isGpdPiD,


   typesCatD, idFunctorD,
   symmInvolD, transReflRD, transReflLD, transAssocD, pathPrecatD,
   idNatD,
   isPropPiD, isContrPiD, isPropToIsSetD, toPathPD,
   refl1D, symm1D, trans1D, transReflR1D, cong01D, cong10D, j01D, j10D,
   congTrans01D, transpTransD]

/-! ## Fast checking with a preloaded definition environment

`buildDefCtx` evaluates every (already-verified) definition **once** into
a shared context; `Raw.resolve` turns each `defn` reference into a de
Bruijn variable, so a use costs one environment lookup and all uses share
one value (which also lets the pointer-equality conversion short-circuits
fire).  This collapses the multiplicative evaluation cost that made the
deep univalence guards infeasible. -/

def buildDefCtx (ds : List LibDef) :
    List String × Ctx × List Val :=
  ds.foldl
    (fun (acc : List String × Ctx × List Val) d =>
      let (names, Γ, env) := acc
      let tyT := (d.ty.resolve names).toOption.getD (.univ 0)
      let tyV := eval env.length env tyT
      let tmT := (d.tm.resolve names).toOption.getD (.univ 0)
      let v := eval env.length env tmT
      (names ++ ["#" ++ d.name], Γ ++ [.tm tyV], env ++ [v]))
    ([], [], [])

def okFast (u : List String × Ctx × List Val) (d : LibDef) : Bool :=
  match checkDefCtx u.1 u.2.1 u.2.2 d.tm d.ty with
  | .ok _ => true
  | .error _ => false

-- sanity: the fast checker agrees on an ordinary definition
#guard okFast (buildDefCtx allDefs) intAsQuotD


/- The deep univalence guards (`uaCompMulD` … `pi1EM1D`) remain infeasible
even with the shared definition environment: the residual cost is
*conversion-time closure re-instantiation* (`capp` allocates fresh values
on every comparison, so pointer sharing never reaches the intermediate
values).  The identified fixes are evaluator-level hash-consing or a
conversion cache — see HANDOFF. -/

#guard allDefs.all (·.ok)

#eval do
  IO.println s!"cubical object-language library: {allDefs.length} definitions, all kernel-checked — incl. the full π₁(S¹) ≅ ℤ"
  for d in allDefs do
    IO.println s!"  ✓ {d.name}"

end Cubical.Library
