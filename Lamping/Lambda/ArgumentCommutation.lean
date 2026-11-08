import Lamping.Lambda.ArgumentParallelCuts
import Lamping.Lambda.FiniteSelectionReindex
import Lamping.Lambda.ProjectionSelections
namespace Lamping.Lambda
/-- A real contraction history outside a subtree preserves that entire
subterm, not just its redex labels. -/
theorem BetaHistory.subterm_fixed_apart (h : BetaHistory ps t u)
    (apart : ∀ p∈ps, DisjointPositions site p) : subtermAt u site=subtermAt t site := by
  induction h with
  | nil => rfl
  | cons first tail ih =>
    obtain ⟨body,arg,lookup,replace⟩ := first
    exact (ih (fun p hp => apart p (List.mem_cons_of_mem _ hp))).trans
      (replaceAt_disjoint (apart _ (List.mem_cons_self ..)).symm replace)

/-- Pull a later chosen-copy contraction across any complete development of
other copies, using an actual parallel-moves square. -/
theorem ParallelStep.pull_inside_step (h : ParallelStep F t u)
    (valid : ∀ p∈F, ∃ z, subtermAt t p=some z ∧ IsRedex z)
    (apart : ∀ r : RedexOcc t, r.val∈F → DisjointPositions site r.val)
    (later : BetaAt u (site++q) w) :
    ∃ (v : Term) (source : BetaAt t (site++q) v)
      (after : ParallelStep ((singleContraction source).residualSet F) v w),
      PermEq ((ParallelHistory.single h).append (.single (singleContraction later)))
        ((ParallelHistory.single (singleContraction source)).append (.single after)) ∧
      ∀ p∈after.paths, DisjointPositions site p := by
  have paths := h.paths_apart apart
  have atChosen : ∀ p∈h.paths, DisjointPositions (site++q) p := by
    intro p hp; exact (paths p hp).descend_left q
  have fixed := h.derivation.valid.subterm_fixed_apart atChosen
  obtain ⟨body,arg,lookup,replace⟩ := later
  have sourceLookup : subtermAt t (site++q)=some (.app (.lam body) arg) := fixed.symm.trans lookup
  obtain ⟨v,hv,_⟩ := replaceAt_lookup sourceLookup (contract body arg)
  let source : BetaAt t (site++q) v := ⟨body,arg,sourceLookup,hv⟩
  let later : BetaAt u (site++q) w := ⟨body,arg,lookup,replace⟩
  obtain ⟨z,afterH,afterS,moves⟩ := parallel_moves h (singleContraction source)
  have sameSelection : ∀ p, p∈h.residualSet [site++q] ↔ p∈[site++q] := by
    rw [h.apart_residualSet_singleton ⟨site++q,source.redex⟩ atChosen]
    exact fun _ => Iff.rfl
  have target := afterH.endpoint_selection (singleContraction later) sameSelection
  subst z
  have realization := PermEq.selection (singleContraction later) afterH (fun p => (sameSelection p).symm)
  refine ⟨v,source,afterS,.trans (.comp (.refl _) realization) moves,?_⟩
  apply afterS.paths_apart
  intro r member
  obtain ⟨old,selected,trace⟩ := (Marked.mem_setResidualPositions F _ r.val).mp member
  let original : RedexOcc t := ⟨old,valid old selected⟩
  have separate := apart original selected
  have residual := ((singleContraction source).residual_iff original r).mpr trace
  have unchanged := (source.disjoint_residual_iff original (separate.descend_left q) r).mp residual
  rw [←unchanged]
  exact separate
end Lamping.Lambda
namespace Lamping.Lambda
/-- Source selections in other copies remain disjoint after a chosen-copy
contraction; membership is proved by actual old-redex residual tracking. -/
theorem BetaAt.residual_selection_apart (source : BetaAt t (site++q) u)
    (valid : ∀ p∈F, ∃ z, subtermAt t p=some z ∧ IsRedex z)
    (apart : ∀ r : RedexOcc t, r.val∈F → DisjointPositions site r.val)
    (r : RedexOcc u) (member : r.val∈(singleContraction source).residualSet F) :
    DisjointPositions site r.val := by
  obtain ⟨old,selected,trace⟩ := (Marked.mem_setResidualPositions F _ r.val).mp member
  let original : RedexOcc t := ⟨old,valid old selected⟩
  have separate := apart original selected
  have residual := ((singleContraction source).residual_iff original r).mpr trace
  have unchanged := (source.disjoint_residual_iff original (separate.descend_left q) r).mp residual
  rw [←unchanged]
  exact separate

/-- A whole specified ordinary copy history can be pulled before a complete
step of the other copies. The lifted ordinary history has the exact same
occurrence schedule; the actual residual development still avoids the copy. -/
theorem Atomic.pull_inside_step {σ : ParallelHistory u w} (atomic : Atomic σ)
    (inside : Internal site σ) (outside : ParallelStep F t u)
    (valid : ∀ p∈F, ∃ z, subtermAt t p=some z ∧ IsRedex z)
    (apart : ∀ r : RedexOcc t, r.val∈F → DisjointPositions site r.val) :
    ∃ (v : Term) (G : List Path) (source : ParallelHistory t v) (after : ParallelStep G v w),
      Atomic source ∧ source.derivation.paths=σ.derivation.paths ∧
      PermEq ((ParallelHistory.single outside).append σ) (source.append (.single after)) ∧
      (∀ p∈G, ∃ z, subtermAt v p=some z ∧ IsRedex z) ∧
      (∀ r : RedexOcc v, r.val∈G → DisjointPositions site r.val) := by
  induction atomic generalizing t F with
  | nil u => exact ⟨t,F,.nil t,outside,.nil t,rfl,.refl _,valid,apart⟩
  | @cons u p mid w tail head htail ih =>
    have location : ∃ q, p=site++q := inside p (by
      simp [ParallelHistory.derivation,ParallelStep.derivation,Derivation.append,singleContraction])
    obtain ⟨q,eq⟩ := location
    subst p
    obtain ⟨v,first,remaining,pull,_⟩ := outside.pull_inside_step valid apart head
    have tailInside : Internal site tail := by
      intro p hp
      exact inside p (by simp [ParallelHistory.derivation,Derivation.append,hp])
    obtain ⟨last,G,source,after,sourceAtomic,same,perm,afterValid,afterApart⟩ :=
      ih tailInside remaining (fun p hp => (singleContraction first).residualSet_valid p hp)
        (first.residual_selection_apart valid apart)
    refine ⟨last,G,.cons (singleContraction first) source,after,.cons first sourceAtomic,?_,?_,afterValid,afterApart⟩
    · change [site++q]++source.derivation.paths=[site++q]++tail.derivation.paths
      rw [same]
    · have initial := pull.append tail
      have rest := PermEq.prepend (ParallelHistory.single (singleContraction first)) perm
      exact .trans (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using initial)
        (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using rest)
end Lamping.Lambda
namespace Lamping.Lambda
/-- Explicit source selections confined to subtrees disjoint from one copy.
It contains no desired factorization, permutation or residual-survival field. -/
inductive ApartHistory (site : Path) : ParallelHistory t u → Prop where
  | nil (t) : ApartHistory site (.nil t)
  | cons (step : ParallelStep F t u) (tail : ParallelHistory u v) :
      (∀ p∈F, ∃ z, subtermAt t p=some z ∧ IsRedex z) →
      (∀ r : RedexOcc t, r.val∈F → DisjointPositions site r.val) →
      ApartHistory site tail → ApartHistory site (.cons step tail)

theorem ApartHistory.append {ρ : ParallelHistory t u} {σ : ParallelHistory u v}
    (h : ApartHistory site ρ) (k : ApartHistory site σ) : ApartHistory site (ρ.append σ) := by
  induction h with
  | nil => exact k
  | cons first tail valid apart rest ih => exact .cons first _ valid apart (ih k)

theorem ApartHistory.paths_apart {ρ : ParallelHistory t u} (h : ApartHistory site ρ) :
    ∀ p∈ρ.derivation.paths, DisjointPositions site p := by
  induction h with
  | nil => simp [ParallelHistory.derivation,Derivation.nil]
  | cons first tail valid apart rest ih =>
    intro p hp
    change p∈first.paths++tail.derivation.paths at hp
    rcases List.mem_append.mp hp with head | later
    · exact first.paths_apart apart p head
    · exact ih p later

/-- Transpose the actual whole row of other-copy steps and a specified
ordinary copy history. The ordinary schedule is preserved exactly. -/
theorem ApartHistory.pull_inside {ρ : ParallelHistory t u} (outside : ApartHistory site ρ)
    {σ : ParallelHistory u w} (atomic : Atomic σ) (inside : Internal site σ) :
    ∃ (v : Term) (source : ParallelHistory t v) (after : ParallelHistory v w),
      Atomic source ∧ source.derivation.paths=σ.derivation.paths ∧
      PermEq (ρ.append σ) (source.append after) ∧ ApartHistory site after := by
  induction outside generalizing w with
  | nil t => exact ⟨w,σ,.nil w,atomic,rfl,by simpa using PermEq.refl σ,.nil w⟩
  | @cons F t u v step tail valid apart rest ih =>
    obtain ⟨mid,copy,row,copyAtomic,sameCopy,permTail,rowApart⟩ := ih atomic inside
    have copyInside : Internal site copy := by
      intro p hp; exact inside p (by rw [←sameCopy]; exact hp)
    obtain ⟨last,G,source,after,sourceAtomic,same,permFirst,afterValid,afterApart⟩ :=
      copyAtomic.pull_inside_step copyInside step valid apart
    refine ⟨last,source,.cons after row,sourceAtomic,same.trans sameCopy,?_,.cons after row afterValid afterApart rowApart⟩
    have first := PermEq.prepend (ParallelHistory.single step) permTail
    have next := permFirst.append row
    exact .trans (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using first)
      (by simpa only [ParallelHistory.append_assoc,ParallelHistory.append,ParallelHistory.single] using next)
end Lamping.Lambda
namespace Lamping.Lambda
/-- Complete actual old-redex survival through all the other-copy reductions,
with its exact chosen-copy occurrence unchanged. -/
theorem ApartHistory.inside_survives {ρ : ParallelHistory t u} (outside : ApartHistory site ρ)
    (r : RedexOcc t) (inside : ∃ q, r.val=site++q) :
    ∃ s : RedexOcc u, s.val=r.val ∧ ρ.derivation.Residual r s := by
  obtain ⟨suffix,atSite⟩ := inside
  have paths : ∀ p∈ρ.derivation.paths, DisjointPositions r.val p := by
    intro p hp; rw [atSite]; exact (outside.paths_apart p hp).descend_left suffix
  obtain ⟨target,tracked,erase⟩ := ρ.derivation.tracked
  have fixed := tracked.trace_fixed_apart paths (fun p hp => (Marked.initial_residual [] t r p).mp hp)
  have alive : r.val∈Marked.tracePositions r.val target := by
    rw [fixed]; exact (Marked.initial_residual [] t r r.val).mpr rfl
  have valid := Marked.tracePositions_sound (tracked.valid (Marked.valid_mark [] t)) alive
  rw [erase] at valid
  exact ⟨⟨r.val,valid⟩,rfl,⟨target,tracked,erase,alive⟩⟩
end Lamping.Lambda
