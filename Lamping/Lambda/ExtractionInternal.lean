import Lamping.Lambda.OrdinarySplits
import Lamping.Lambda.ProjectionSelections
import Lamping.Lambda.ParallelPrefixScope
import Lamping.Lambda.StepProjectionHead
namespace Lamping.Lambda

theorem Internal.append_iff (ρ : ParallelHistory m t) (σ : ParallelHistory t u) :
    Internal site (ρ.append σ) ↔ Internal site ρ ∧ Internal site σ := by
  simp only [Internal, ParallelHistory.derivation_append, Derivation.append, List.mem_append]
  constructor
  · intro h
    exact ⟨fun p hp => h p (.inl hp), fun p hp => h p (.inr hp)⟩
  · rintro ⟨hρ, hσ⟩ p hp
    exact hp.elim (hρ p) (hσ p)

theorem Internal.single_iff (R : BetaAt t p u) :
    Internal site (.single (singleContraction R)) ↔ ∃ q, p = site ++ q := by
  constructor
  · intro h; exact h p (by change p ∈ [p]; exact List.mem_singleton_self _)
  · intro h q hq
    change q ∈ [p] at hq
    cases List.mem_singleton.mp hq
    exact h

/-- A scoped actual history cannot bring an old redex from outside its
 fixed subtree into that subtree. -/
theorem ParallelHistory.residual_reflect_internal (ρ : ParallelHistory t u)
    (inside : Internal site ρ) (r : RedexOcc t) (s : RedexOcc u)
    (hs : ∃ q, s.val = site ++ q) (residual : ρ.derivation.Residual r s) :
    ∃ q, r.val = site ++ q := by
  classical
  by_cases hr : ∃ q, r.val = site ++ q
  · exact hr
  · have he := (ρ.residual_outside_internal inside r s hr).mp residual
    obtain ⟨q, hq⟩ := hs
    exact False.elim (hr ⟨q, he.trans hq⟩)

/-- Rule (i) preserves actual internality, including when its chosen old
 predecessor is obtained by inverse residual transport. -/
theorem residual_extraction_internal (ρ : ParallelHistory m t)
    (R : BetaAt t p u) (S : BetaAt u q v) (S' : BetaAt t q' v')
    (residual : (singleContraction R).derivation.Residual ⟨q', S'.redex⟩ ⟨q, S.redex⟩)
    (inside : Internal site ((ρ.append (.single (singleContraction R))).append
      (.single (singleContraction S)))) :
    Internal site (ρ.append (.single (singleContraction S'))) := by
  obtain ⟨hρR, hS⟩ := (Internal.append_iff _ _).mp inside
  obtain ⟨hρ, hR⟩ := (Internal.append_iff _ _).mp hρR
  apply (Internal.append_iff _ _).mpr
  refine ⟨hρ, (Internal.single_iff S').mpr ?_⟩
  exact (ParallelHistory.single (singleContraction R)).residual_reflect_internal hR
    ⟨q', S'.redex⟩ ⟨q, S.redex⟩ ((Internal.single_iff S).mp hS) residual

/-- An ordinary horizontal row reflected across a development confined to a
 fixed subtree is internal whenever its actual projected history is internal.
 This inverts positions using old identities, not endpoint subterm equality. -/
theorem StepProjection.internal_reflect {step : ParallelStep F t u}
    {σ : ParallelHistory t v} {τ : ParallelHistory u w} {last : ParallelStep G v w}
    (row : StepProjection step σ τ last) (ha : Atomic σ) (hb : Atomic τ)
    (lookup : ∃ a, subtermAt t site = some a)
    (scope : ∀ p ∈ F, ∃ q, p = site ++ q) (inside : Internal site τ) : Internal site σ := by
  induction ha generalizing F u w G with
  | nil => intro q hq; change q ∈ [] at hq; cases hq
  | @cons t q v target tail S htail ih =>
    cases hb with
    | nil =>
      have hlen := row.length
      simp [ParallelHistory.length] at hlen
      omega
    | @cons u q' mid target' tail' B htail' =>
      obtain ⟨sq, hfirst, htop, _, hside, remaining⟩ := row.head_square
      cases sq with
      | mk first top side vertical =>
        cases hfirst
        cases htop
        obtain ⟨a, hlookup⟩ := lookup
        have stepInside : Internal site (.single first) := by
          intro z hz
          simp only [ParallelHistory.single, ParallelHistory.derivation, Derivation.append,
            Derivation.nil, List.append_nil] at hz
          exact first.paths_scope scope hlookup z hz
        obtain ⟨ps, hps⟩ := stepInside.paths_prefix
        simp only [ParallelHistory.single, ParallelHistory.derivation, Derivation.append,
          Derivation.nil, List.append_nil] at hps
        have sidePaths : side.paths = [q'] := by
          have hp := congrArg Derivation.paths hside
          exact hp
        have pred := first.singleton_projection_residual ⟨q, S.redex⟩ ⟨q', B.redex⟩ side sidePaths
        have bottomFirst : ∃ s, q' = site ++ s := inside q' (by
          change q' ∈ q' :: tail'.derivation.paths
          exact List.mem_cons_self)
        have topFirst : ∃ s, q = site ++ s := by
          classical
          by_cases hq : ∃ s, q = site ++ s
          · exact hq
          · have fixed := first.derivation.prefix_residual_outside_source hps
              ⟨q, S.redex⟩ ⟨q', B.redex⟩ hq pred
            obtain ⟨s, hs⟩ := bottomFirst
            exact False.elim (hq ⟨s, fixed.trans hs⟩)
        obtain ⟨localPath, hlocal⟩ := topFirst
        have newLookup : ∃ b, subtermAt v site = some b := by
          have S' : BetaAt t (site ++ localPath) v := hlocal ▸ S
          obtain ⟨b, _, _, hb⟩ := S'.prefix_reflect hlookup
          exact ⟨b, hb⟩
        have newScope : ∀ z ∈ (singleContraction S).residualSet F, ∃ s, z = site ++ s := by
          intro z hz
          obtain ⟨old, hold, htrace⟩ := (Marked.mem_setResidualPositions F _ z).mp hz
          obtain ⟨localOld, hOld⟩ := scope old hold
          have hz' : z ∈ (singleContraction S).residualSet [site ++ localOld] := by
            apply (Marked.mem_setResidualPositions _ _ _).mpr
            exact ⟨old, by simp only [hOld, List.mem_singleton], htrace⟩
          exact (singleContraction S).residualSet_has_prefix
            (ps := [localPath]) (by change [q] = _; simp only [List.map_cons, List.map_nil, hlocal]) hz'
        have tailInside : Internal site tail' := by
          intro z hz
          exact inside z (by change z ∈ q' :: tail'.derivation.paths; exact List.mem_cons_of_mem _ hz)
        have topTail := ih remaining htail' newLookup newScope tailInside
        intro z hz
        change z ∈ q :: tail.derivation.paths at hz
        rcases List.mem_cons.mp hz with he | he
        · cases he; exact ⟨localPath, hlocal⟩
        · exact topTail z he
private theorem source_scope_lookup (R : BetaAt t p u) (hp : ∃ q, p = site ++ q) :
    ∃ a, subtermAt t site = some a := by
  obtain ⟨q, hq⟩ := hp
  obtain ⟨a, ha, _⟩ := R.redex
  rw [hq] at ha
  obtain ⟨b, hb, _⟩ := prefix_exists ha
  exact ⟨b, hb⟩

private theorem projection_extraction_internal (ρ : ParallelHistory m t)
    (R : BetaAt t p u) (σ : ParallelHistory t v) (ha : Atomic σ)
    (τ : ParallelHistory u w) (hb : Atomic τ) (last : ParallelStep G v w)
    (row : StepProjection (singleContraction R) σ τ last)
    (inside : Internal site ((ρ.append (.single (singleContraction R))).append τ)) :
    Internal site (ρ.append σ) := by
  obtain ⟨hρR, hτ⟩ := (Internal.append_iff _ _).mp inside
  obtain ⟨hρ, hR⟩ := (Internal.append_iff _ _).mp hρR
  have hp := (Internal.single_iff R).mp hR
  apply (Internal.append_iff _ _).mpr
  refine ⟨hρ, row.internal_reflect ha hb (source_scope_lookup R hp) ?_ hτ⟩
  intro q hq
  cases List.mem_singleton.mp hq
  exact hp

/-- All four source rules preserve confinement to a fixed actual subtree.
 In particular the reverse projection cases reflect old identities rather than
 assuming that an extraction target stays inside the source region. -/
theorem ExtractionStep.internal (h : ExtractionStep r s)
    (inside : Internal site r.history) : Internal site s.history := by
  cases h with
  | residual ρ hρ R S S' hs => exact residual_extraction_internal ρ R S S' hs inside
  | disjoint ρ hρ R σ hσ σ' hσ' last row positive region apart internal =>
    exact projection_extraction_internal ρ R σ hσ σ' hσ' last row inside
  | functionPart ρ hρ R σ hσ σ' hσ' last row positive internal =>
    exact projection_extraction_internal ρ R σ hσ σ' hσ' last row inside
  | argumentPart ρ hρ R σ hσ σ' hσ' positive lift =>
    obtain ⟨hρR, _⟩ := (Internal.append_iff _ _).mp inside
    obtain ⟨hρ, hR⟩ := (Internal.append_iff _ _).mp hρR
    obtain ⟨localPath, hp⟩ := (Internal.single_iff R).mp hR
    apply (Internal.append_iff _ _).mpr
    refine ⟨hρ, ?_⟩
    intro q hq
    rw [lift.original_paths] at hq
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hq
    exact ⟨localPath ++ [.arg] ++ z, by simp only [hp, List.append_assoc]⟩

theorem Extraction.internal (h : Extraction r s) (inside : Internal site r.history) :
    Internal site s.history := by
  induction h with
  | refl => exact inside
  | cons h hs ih => exact ih (h.internal inside)
end Lamping.Lambda
