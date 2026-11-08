import Lamping.Lambda.BetaPreimageErasure
namespace Lamping.Checks.BetaPreimageErasure
open Lambda Lambda.Labelled
private abbrev a := Label.atom 9
private def body : LTerm := .app a (.lam a (.var a 1)) (.var a 0)
private def otherBody : LTerm := .app (.atom 0) (.lam (.atom 1) (.var (.atom 2) 1)) (.var (.atom 3) 0)
private def identity : LTerm := .lam a (.var a 0)
private def argument : LTerm := .app a identity identity
private def otherArgument : LTerm := .app (.atom 4)
  (.lam (.atom 5) (.var (.atom 6) 0)) (.lam (.atom 7) (.var (.atom 8) 0))
private abbrev site : Path := [.body]
private def source : LTerm := .lam a (.app a (.lam a body) argument)
private def target : LTerm := .lam a (LTerm.contract a a body argument)
private def otherSource : LTerm := .lam (.atom 20)
  (.app (.atom 21) (.lam (.atom 22) otherBody) otherArgument)
private def otherTarget : LTerm := .lam (.atom 20)
  (LTerm.contract (.atom 21) (.atom 22) otherBody otherArgument)
private def turn : StepAt site source target := .body (.root _ _ _ _)
private def otherTurn : StepAt site otherSource otherTarget := .body (.root _ _ _ _)
private theorem bodySame : body.erase=otherBody.erase := rfl
private theorem argumentSame : argument.erase=otherArgument.erase := rfl
private def contextOrigin : BetaNodePreimage body argument site [] [] :=
  .context (by rintro ⟨rest,impossible⟩;cases impossible)
private def retainedOrigin : BetaNodePreimage body argument site
    (site++[.fn]) ((site++[.fn,.body])++[.fn]) :=
  .retained rfl (by intro stamp impossible;cases impossible)
private def copiedOrigin : BetaNodePreimage body argument site
    ((site++[.fn,.body])++[.fn,.body]) ((site++[.arg])++[.fn,.body]) :=
  .copied rfl rfl

/-- Two genuine nonroot beta events have the same erased source and are
closed. Different annotations do not change the exact origin coordinates. -/
theorem actual_context_retained_and_copy :
    StepAt site source target ∧StepAt site otherSource otherTarget ∧
    Closed source.erase ∧Closed otherSource.erase ∧source.erase=otherSource.erase ∧
    BetaNodePreimage otherBody otherArgument site [] [] ∧
    BetaNodePreimage otherBody otherArgument site
      (site++[.fn]) ((site++[.fn,.body])++[.fn]) ∧
    BetaNodePreimage otherBody otherArgument site
      ((site++[.fn,.body])++[.fn,.body]) ((site++[.arg])++[.fn,.body]) := by
  exact ⟨turn,otherTurn,by change ((1<3) ∧(0<2)) ∧((0<2) ∧(0<2));decide,
    by change ((1<3) ∧(0<2)) ∧((0<2) ∧(0<2));decide,rfl,
    contextOrigin.reannotate bodySame argumentSame,
    retainedOrigin.reannotate bodySame argumentSame,
    copiedOrigin.reannotate bodySame argumentSame⟩

/-- This actual copied binder variable has the specified old ARG-internal
coordinate in BOTH annotations. A different coordinate cannot be substituted. -/
theorem actual_strict_copy_coordinate {otherOld : Path}
    (actual : BetaNodePreimage otherBody otherArgument site
      ((site++[.fn,.body])++[.fn,.body]) otherOld) :
    (site++[.arg])++[.fn,.body]=otherOld :=
  copiedOrigin.unique_of_same_erase bodySame argumentSame actual

private def orderedOrigins : BetaEdgePreimages body argument site
    [[],site++[.fn],(site++[.fn,.body])++[.fn,.body]]
    [[],(site++[.fn,.body])++[.fn],(site++[.arg])++[.fn,.body]] :=
  .cons contextOrigin (.cons retainedOrigin (.cons copiedOrigin .nil))

theorem actual_ordered_origins : BetaEdgePreimages otherBody otherArgument site
    [[],site++[.fn],(site++[.fn,.body])++[.fn,.body]]
    [[],(site++[.fn,.body])++[.fn],(site++[.arg])++[.fn,.body]] :=
  orderedOrigins.reannotate bodySame argumentSame

/-- The two different copied roots really share the same old ARG root.
Coordinate uniqueness at a fixed current occurrence is not global injectivity. -/
theorem actual_shared_argument_preimage :
    site++[.arg]≠site++[.fn,.body] ∧
    BetaNodePreimage otherBody otherArgument site (site++[.arg]) (site++[.arg]) ∧
    BetaNodePreimage otherBody otherArgument site (site++[.fn,.body]) (site++[.arg]) := by
  have left : BetaNodePreimage body argument site (site++[.arg]) (site++[.arg]) :=
    .copied (q:=[.arg]) (relative:=[]) rfl rfl
  have right : BetaNodePreimage body argument site (site++[.fn,.body]) (site++[.arg]) :=
    .copied (q:=[.fn,.body]) (relative:=[]) rfl rfl
  exact ⟨by decide,left.reannotate bodySame argumentSame,right.reannotate bodySame argumentSame⟩

theorem actual_created_status :
    BetaCreatedIncoming otherBody site (site++[.arg]) ∧
    ¬BetaCreatedIncoming otherBody site ((site++[.fn,.body])++[.fn,.body]) := by
  constructor
  · exact (betaCreatedIncoming_of_same_erase bodySame).mp (by decide)
  · intro created
    have oldCreated := (betaCreatedIncoming_of_same_erase bodySame).mpr created
    have notOld : ¬BetaCreatedIncoming body site ((site++[.fn,.body])++[.fn,.body]) := by decide
    exact notOld oldCreated

#print axioms BetaNodePreimage.reannotate
#print axioms BetaNodePreimage.unique_of_same_erase
#print axioms BetaEdgePreimages.reannotate
#print axioms betaCreatedIncoming_of_same_erase
#print axioms actual_context_retained_and_copy
#print axioms actual_strict_copy_coordinate
#print axioms actual_ordered_origins
#print axioms actual_shared_argument_preimage
#print axioms actual_created_status
end Lamping.Checks.BetaPreimageErasure
