import Lamping.Lamping.ActionSourceDirection
import Lamping.Lamping.ChainRepresentation
import Lamping.Lamping.TraceSeams
namespace Lamping.AG
open Graph Lambda
private theorem forward_auxiliary_app {f : Op} {i : Nat} {p q : Aux f} {a b : Context}
    (rule : Traversal i (.op f) (.inr p) (.inr q) a b)
    (direction : ForwardPorts (.op f) (.inr p) (.inr q)) :
    f=.app ∧HEq p false ∧HEq q true := by
  cases f with
  | app =>
    refine ⟨rfl,heq_of_eq (Sum.inr.inj direction.1),?_⟩
    rcases direction.2 with impossible|same
    · cases impossible
    · exact heq_of_eq (Sum.inr.inj same)
  | lam => cases direction.1
  | fan => exact False.elim rule.aux_aux
  | cro => exact False.elim rule.aux_aux
  | bra => exact False.elim rule.aux_aux

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- The first departure is deliberately skipped; every later actual segment
in an empty-word path has empty token emission. -/
theorem empty_word_later_emission {pre post : List (Endpoint g)} {e : Endpoint g}
    (nonempty : pre≠[]) (empty : accessWord g (pre++e::post)=[]) : arrivalWord g e=[] := by
  cases pre with
  | nil => exact False.elim (nonempty rfl)
  | cons h pre =>
    simp only [List.cons_append,accessWord,List.flatMap_append,List.flatMap_cons] at empty
    exact (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp empty).2).1
end

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- A complete labelled forward passive passage necessarily emits the
application-argument token. It cannot occur inside an empty-word piece. -/
theorem PathSite.no_passive_in_empty_word {pre post : List (Endpoint site.net)}
    (p q : Aux s.passive) {a b : Context}
    (labels : Labelling site.net
      (pre++site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::.inl ⟨.inr (.inr ()),.inr q⟩::post) a b)
    (forward : Forward site.net
      (pre++site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::.inl ⟨.inr (.inr ()),.inr q⟩::post))
    (empty : accessWord site.net
      (pre++site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::.inl ⟨.inr (.inr ()),.inr q⟩::post)=[]) : False := by
  obtain ⟨middle,_before,after⟩ := labels.split_segment
  have suffix := forward.suffix_at pre.length (site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)) (by simp)
  simp only [List.drop_append_of_le_length (Nat.le_refl _),List.drop_length,List.nil_append] at suffix
  have direction := Forward.actual_node_ports (g:=site.net) (.inr (.inr ())) (.inr p) (.inr q) post suffix
  have turn : ∃ output, Traversal s.high (.op s.passive) (.inr p) (.inr q) middle output := by
    cases after with
    | cons turn rest =>
      rw [Pairing.involutive] at turn
      cases turn with | node node x y rule => exact ⟨_,rule⟩
  obtain ⟨output,rule⟩ := turn
  obtain ⟨op,_inputRole,outputRole⟩ := forward_auxiliary_app rule direction
  have emitted := empty_word_later_emission
    (pre:=pre++[site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)]) (e:=.inl ⟨.inr (.inr ()),.inr q⟩)
    (by simp) (by simpa only [List.append_assoc,List.singleton_append] using empty)
  cases s <;> cases op <;> have same : q=true := eq_of_heq outputRole <;> subst q <;> change [Step.arg]=[] at emitted <;> cases emitted

/-- Every actual syntax fragment has its own empty word and labelled
Forward path; the no-passive conclusion is for this literal occurrence. -/
theorem SourceEdgeFragment.no_complete_passive
    {root : B} {current : Labelled.LTerm} {edge : Labelled.SourceEdge} {position : Path}
    (fragment : SourceEdgeFragment current site.net root edge position)
    (p q : Aux s.passive) (pre post : List (Endpoint site.net)) :
    fragment.segments≠pre++site.net.wire (.inl ⟨.inr (.inr ()),.inr p⟩)::
      .inl ⟨.inr (.inr ()),.inr q⟩::post := by
  intro same
  obtain ⟨a,b,whole⟩ := fragment.access.property.1.1
  obtain ⟨middle,_before,piece⟩ := fragment.assignments a b whole
  exact site.no_passive_in_empty_word p q (same ▸ piece) (same ▸ fragment.forward)
    (same ▸ fragment.emptyWord)
end
end Lamping.AG