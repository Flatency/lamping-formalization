import Lamping.Lambda.BetaPreimageLabels
namespace Lamping.Lambda.Labelled

private theorem lookup_of_same_erase {left right node : LTerm}
    (same : left.erase=right.erase) (lookup : left.subterm p=some node) :
    ∃ other,right.subterm p=some other ∧other.erase=node.erase := by
  have bare : subtermAt right.erase p=some node.erase := by
    rw [←same,←LTerm.erase_subterm,lookup];rfl
  rw [←LTerm.erase_subterm] at bare
  exact Option.map_eq_some_iff.mp bare

private theorem nonselected_of_same_erase {left right : LTerm} {depth : Nat}
    (same : right.erase=left.erase)
    (nonselected : ∀ stamp,left≠.var stamp depth) : ∀ stamp,right≠.var stamp depth := by
  intro stamp equal
  have erased : left.erase=.var depth := same.symm.trans (congrArg LTerm.erase equal)
  cases left with
  | var label index => exact nonselected label (by rw [Term.var.inj erased])
  | lam label body => cases erased
  | app label fn arg => cases erased

/-- Actual beta origins depend on occurrence coordinates and erased
constructor/binder data. Re-annotation retains the SAME old coordinate. -/
theorem BetaNodePreimage.reannotate {body argument otherBody otherArgument : LTerm}
    (bodySame : body.erase=otherBody.erase) (argumentSame : argument.erase=otherArgument.erase)
    (origin : BetaNodePreimage body argument site current oldPosition) :
    BetaNodePreimage otherBody otherArgument site current oldPosition := by
  cases origin with
  | context outside => exact .context outside
  | retained lookup nonselected =>
    obtain ⟨other,otherLookup,same⟩ := lookup_of_same_erase bodySame lookup
    exact .retained otherLookup (nonselected_of_same_erase same nonselected)
  | copied occurs lookup =>
    obtain ⟨other,otherLookup,_same⟩ := lookup_of_same_erase argumentSame lookup
    exact .copied (by rw [←bodySame];exact occurs) otherLookup

theorem BetaNodePreimage.unique_of_same_erase {body argument otherBody otherArgument : LTerm}
    (bodySame : body.erase=otherBody.erase) (argumentSame : argument.erase=otherArgument.erase)
    (first : BetaNodePreimage body argument site current left)
    (second : BetaNodePreimage otherBody otherArgument site current right) : left=right :=
  (first.reannotate bodySame argumentSame).unique second

theorem BetaEdgePreimages.reannotate {body argument otherBody otherArgument : LTerm}
    (bodySame : body.erase=otherBody.erase) (argumentSame : argument.erase=otherArgument.erase)
    (origins : BetaEdgePreimages body argument site edges oldEdges) :
    BetaEdgePreimages otherBody otherArgument site edges oldEdges := by
  induction origins with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.reannotate bodySame argumentSame) ih

theorem betaCreatedIncoming_of_same_erase {body otherBody : LTerm}
    (same : body.erase=otherBody.erase) :
    BetaCreatedIncoming body site edge ↔BetaCreatedIncoming otherBody site edge := by
  unfold BetaCreatedIncoming
  rw [same]
end Lamping.Lambda.Labelled
