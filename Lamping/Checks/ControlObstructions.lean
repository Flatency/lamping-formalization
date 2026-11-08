import Lamping.Lamping.ControlPrincipalObstruction
namespace Lamping.Checks.ControlObstructions
open AG Graph

private def labels : Bool → Label signature | false => label .lam 1 | true => label .cro 1
/-- A synthetic countercheck, not an encoding or a reachable-graph claim. -/
private def graph : Net signature Bool Unit Empty where
  label := labels
  wire := {
    mate := fun e => match e with
      | .inl ⟨false,.inl ()⟩ => .inr (.inl ())
      | .inl ⟨false,.inr false⟩ => .inl ⟨true,.inr ()⟩
      | .inl ⟨false,.inr true⟩ => .inl ⟨true,.inl ()⟩
      | .inl ⟨true,.inl ()⟩ => .inl ⟨false,.inr true⟩
      | .inl ⟨true,.inr ()⟩ => .inl ⟨false,.inr false⟩
      | .inr (.inl ()) => .inl ⟨false,.inl ()⟩
      | .inr (.inr ⟨w,_⟩) => nomatch w
    involutive := by
      rintro (⟨node,port⟩ | (boundary | ⟨w,d⟩))
      · cases node <;> cases port <;> first | rfl | rename_i bit; cases bit <;> rfl
      · cases boundary; rfl
      · exact nomatch w
    fixedPointFree := by
      rintro (⟨node,port⟩ | (boundary | ⟨w,d⟩))
      · cases node <;> cases port <;> first | (intro impossible; cases impossible) | rename_i bit; cases bit <;> (intro impossible; cases impossible)
      · intro impossible; cases impossible
      · exact nomatch w }

private abbrev body : Endpoint graph := .inl ⟨false,lamBody⟩
private abbrev bind : Endpoint graph := .inl ⟨false,lamBind⟩
private abbrev croAux : Endpoint graph := .inl ⟨true,.inr ()⟩

private theorem path_labels : Labelling graph [body,croAux] Context.empty Context.empty := by
  have emptyAt : Context.empty.replace 1 Context.empty=Context.empty := by
    ext k
    simp [Context.replace]
  have cro : Passage 1 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
    simpa only [Context.cons_empty,emptyAt] using Passage.cro (i:=1) Context.empty Context.empty
  exact .cons (LabelledTurn.node (g:=graph) true (.inl ()) (.inr ()) (.inverse cro)) (.single _ _)

-- A genuine labelled and Forward loop can still violate the complete
-- arbitrary-source-input clause of Independence.
example : ProperPath graph [body,croAux] := ⟨_,_,path_labels⟩
example : ¬Independence graph () := by
  intro indep
  exact indep.no_high_control_principal body croAux bind [] .lamBody .lamBind 1 1
    (AtProperRole.lamBody (g:=graph) false AG.lamBody 1 rfl HEq.rfl) True.intro
    (AtProperRole.lamBind (g:=graph) false AG.lamBind 1 rfl HEq.rfl) True.intro rfl
    (.node true (.inl ()) (.inr ()) rfl rfl True.intro (.single _)) path_labels
    true (.inl ()) .cro 1 rfl (Or.inr (Or.inl rfl)) HEq.rfl rfl (Nat.le_refl 1)

#print axioms Independence.no_high_control_principal
end Lamping.Checks.ControlObstructions
