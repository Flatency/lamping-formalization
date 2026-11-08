import Lamping.Lamping.MatchedControlInputs
namespace Lamping.AG
open Graph Lambda

/-- A supplied actual inverse-control traversal discharges the low marker
constraint of this very fixed fan branch, with exact input/output context. -/
theorem fanAction_passive_replay (i j : Nat) (branch : Bool) (a middle : Context)
    (rule : Traversal i (.op .fan) (.inl ()) (.inr branch) a middle) :
    Labelling (fanRight .app i j)
      [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr branch⟩,
        .inl ⟨.inl branch,appArg⟩,.inl ⟨.inr true,.inl ()⟩] a a :=
  .cons (LabelledTurn.node (g:=fanRight .app i j) (.inr false) (.inl ()) (.inr branch) rule)
    (.cons (LabelledTurn.node (g:=fanRight .app i j) (.inl branch) appCtx appArg (.direct (.appArg middle)))
      (.cons (LabelledTurn.node (g:=fanRight .app i j) (.inr true) (.inr branch) (.inl ()) rule.reverse)
        (.single _ _)))

theorem unaryAction_passive_replay (control : Op) (single : Bij Unit (Aux control))
    (i k : Nat) (a middle : Context)
    (rule : Traversal i (.op control) (.inl ()) (.inr (single ())) a middle) :
    Labelling (unaryRightCore control .app single i k)
      [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr (single ())⟩,
        .inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩] a a :=
  .cons (LabelledTurn.node (g:=unaryRightCore control .app single i k) (.inr false) (.inl ()) (.inr (single ())) rule)
    (.cons (LabelledTurn.node (g:=unaryRightCore control .app single i k) (.inl ()) appCtx appArg (.direct (.appArg middle)))
      (.cons (LabelledTurn.node (g:=unaryRightCore control .app single i k) (.inr true) (.inr (single ())) (.inl ()) rule.reverse)
        (.single _ _)))

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j} {root : B} {t : Term}

/-- Matches supplies a specific syntax function child, so every new labelling
of the SAME actual parent supports the original fixed passive fan excursion.
The reference inverse turn is real; arbitrary old labels alone are insufficient. -/
theorem PathSite.fan_matched_passive_replay
    (site : PathSite (.fanAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (parent : RootAccess site.net root)
    (finish : parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)))
    (branch : Bool) (referenceInput referenceSeam referenceOutput : Context)
    (referenceParent : Labelling site.net parent.val referenceInput referenceSeam)
    (reference : Traversal i (.op .fan) (.inl ()) (.inr branch) referenceSeam referenceOutput) :
    ∀ requested seam,Labelling site.net parent.val requested seam →
      Labelling (fanRight .app i j)
        [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr branch⟩,
          .inl ⟨.inl branch,appArg⟩,.inl ⟨.inr true,.inl ()⟩] seam seam := by
  have stable := site.matched_control_input matching indep (Or.inl rfl) rfl parent appCtx HEq.rfl
    finish branch referenceInput referenceSeam referenceOutput referenceParent reference
  intro requested seam labels
  obtain ⟨middle,rule⟩ := stable requested seam labels
  exact fanAction_passive_replay i j branch seam middle rule

theorem PathSite.cro_matched_passive_replay
    (site : PathSite (.croAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (parent : RootAccess site.net root)
    (finish : parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)))
    (referenceInput referenceSeam referenceOutput : Context)
    (referenceParent : Labelling site.net parent.val referenceInput referenceSeam)
    (reference : Traversal i (.op .cro) (.inl ()) (.inr ()) referenceSeam referenceOutput) :
    ∀ requested seam,Labelling site.net parent.val requested seam →
      Labelling (unaryRightCore .cro .app (Bij.refl _) i (j-1))
        [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr ()⟩,
          .inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩] seam seam := by
  have stable := site.matched_control_input matching indep (Or.inr (Or.inl rfl)) rfl parent appCtx HEq.rfl
    finish () referenceInput referenceSeam referenceOutput referenceParent reference
  intro requested seam labels
  obtain ⟨middle,rule⟩ := stable requested seam labels
  exact unaryAction_passive_replay .cro (Bij.refl _) i (j-1) seam middle rule

theorem PathSite.bra_matched_passive_replay
    (site : PathSite (.braAction .app i j lt) kept (B:=B) (W:=W) (V:=V))
    (matching : Matches site.net root t) (indep : Independence site.net root)
    (parent : RootAccess site.net root)
    (finish : parent.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),appCtx⟩)))
    (referenceInput referenceSeam referenceOutput : Context)
    (referenceParent : Labelling site.net parent.val referenceInput referenceSeam)
    (reference : Traversal i (.op .bra) (.inl ()) (.inr ()) referenceSeam referenceOutput) :
    ∀ requested seam,Labelling site.net parent.val requested seam →
      Labelling (unaryRightCore .bra .app (Bij.refl _) i (j+1))
        [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr ()⟩,
          .inl ⟨.inl (),appArg⟩,.inl ⟨.inr true,.inl ()⟩] seam seam := by
  have stable := site.matched_control_input matching indep (Or.inr (Or.inr rfl)) rfl parent appCtx HEq.rfl
    finish () referenceInput referenceSeam referenceOutput referenceParent reference
  intro requested seam labels
  obtain ⟨middle,rule⟩ := stable requested seam labels
  exact unaryAction_passive_replay .bra (Bij.refl _) i (j+1) seam middle rule
end
end Lamping.AG
