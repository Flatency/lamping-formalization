import Lamping.Lambda.ParallelContextLift
namespace Lamping.Lambda.Marked

/-- The occurrence tree fixes trace order; equal membership alone is used
only after equality of the erased passive trees has been established. -/
theorem trace_eq_of_members (he : t.erase=u.erase)
    (members : ∀ q, q∈tracePositions r t ↔ q∈tracePositions s u) :
    tracePositions r t=tracePositions s u := by
  suffices core : ∀ t u : Marked, t.passive=t → u.passive=u → t.erase=u.erase →
      (∀ q, q∈tracePositions r t ↔ q∈tracePositions s u) →
      tracePositions r t=tracePositions s u by
    simpa only [passive_trace] using core t.passive u.passive
      (passive_idempotent t) (passive_idempotent u)
      (by simpa only [passive_erase] using he)
      (by simpa only [passive_trace] using members)
  intro t
  induction t with
  | var i =>
    intro u _ hu he _
    cases u <;> simp only [erase,Term.var.injEq,reduceCtorEq] at he
    rfl
  | red => intro u ht; cases ht
  | lam b ih =>
    intro u ht hu he members
    cases u with
    | var => cases he
    | app => cases he
    | red => cases he
    | lam c =>
      have hb := ih c (Marked.lam.inj ht) (Marked.lam.inj hu) (Term.lam.inj he)
        (fun q => by simpa [tracePositions] using members (.body::q))
      simp only [tracePositions,hb]
  | app l f a hf ha =>
    intro u ht hu he members
    cases u with
    | var => cases he
    | lam => cases he
    | red => cases hu
    | app k g b =>
      have root : r∈l ↔ s∈k := by simpa [tracePositions] using members []
      have fe := hf g (Marked.app.inj ht).2.1 (Marked.app.inj hu).2.1
        (Term.app.inj he).1 (fun q => by simpa [tracePositions] using members (.fn::q))
      have ae := ha b (Marked.app.inj ht).2.2 (Marked.app.inj hu).2.2
        (Term.app.inj he).2 (fun q => by simpa [tracePositions] using members (.arg::q))
      simp only [tracePositions,fe,ae,root]

private theorem child_trace_eq (hp : childAt t e=some a) (pass : t.passive=t)
    (scope : ∀ z∈tracePositions r t, ∃ q,z=e::q) :
    tracePositions r t=(tracePositions r a).map (e::·) := by
  have root (l : List Path) (rest : List Path)
      (ht : tracePositions r t=(if r∈l then [[]] else [])++rest) : r∉l := by
    intro hr
    have hz : []∈tracePositions r t := by simp [ht,hr]
    obtain ⟨q,hq⟩ := scope [] hz
    cases hq
  cases t with
  | var i => cases e <;> cases hp
  | red => cases pass
  | lam b => cases e with
    | fn => cases hp
    | arg => cases hp
    | body => cases hp; rfl
  | app l f b => cases e with
    | body => cases hp
    | fn =>
      cases hp
      have rn := root l _ rfl
      have empty : tracePositions r b=[] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro q hq
        obtain ⟨z,hz⟩ := scope (.arg::q) (by simp [tracePositions,hq])
        cases hz
      simp [tracePositions,rn,empty]
    | arg =>
      cases hp
      have rn := root l _ rfl
      have empty : tracePositions r f=[] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro q hq
        obtain ⟨z,hz⟩ := scope (.fn::q) (by simp [tracePositions,hq])
        cases hz
      simp [tracePositions,rn,empty]

theorem subtree_trace_eq (hp : subtreeAt t pre=some a) (pass : t.passive=t)
    (scope : ∀ z∈tracePositions r t, ∃ q,z=pre++q) :
    tracePositions r t=(tracePositions r a).map (fun q => pre++q) := by
  induction pre generalizing t with
  | nil => cases hp; simp
  | cons e pre ih =>
    cases hc : childAt t e with
    | none => simp [subtreeAt,hc] at hp
    | some c =>
      have cp : subtreeAt c pre=some a := by simpa [subtreeAt,hc] using hp
      have passC : c.passive=c := by
        cases t <;> cases e <;> simp [childAt] at hc <;>
          try cases pass
        all_goals subst c; simp_all [passive]
      have childScope : ∀ z∈tracePositions r c, ∃ q,z=pre++q := by
        intro z hz
        have global : e::z∈tracePositions r t := by
          simpa only [List.singleton_append] using
            (subtreeAt_trace (p:=[e]) (by simp [subtreeAt,hc])).mp hz
        obtain ⟨q,hq⟩ := scope (e::z) global
        exact ⟨q,(List.cons.inj hq).2⟩
      rw [child_trace_eq hc pass (by
        intro z hz
        obtain ⟨q,hq⟩ := scope z hz
        exact ⟨pre++q,hq⟩),ih cp passC childScope]
      simp only [List.map_map,Function.comp_def,List.cons_append]

end Lamping.Lambda.Marked

namespace Lamping.Lambda

/-- Literal ordered traces in a context, for arbitrary old names. Selection
lists need not be related: the specified actual schedules carry the names. -/
theorem ParallelStep.trace_prefix_eq (h : ParallelStep F a b) (H : ParallelStep K t u)
    (hp : subtermAt t pre=some a)
    (paths : H.paths=h.paths.map (fun q => pre++q)) (r : Path) :
    Marked.tracePositions (pre++r) H.markedTarget=
      (Marked.tracePositions r h.markedTarget).map (fun q => pre++q) := by
  have global : Marked.History (h.paths.map (fun q => pre++q))
      (Marked.mark [] t) H.markedTarget.passive := by
    simpa only [paths] using H.tracked
  have init : Marked.subtreeAt (Marked.mark [] t) pre=some (Marked.markAt [] a pre) := by
    simpa only [Marked.mark,List.nil_append] using Marked.subtreeAt_markAt hp []
  obtain ⟨slice,localHistory,lookup⟩ := global.prefix_reflect init
  have initialShape : (Marked.markAt [] a pre).skeleton=(Marked.mark [] a).skeleton := by
    apply Marked.skeleton_of_shape
    · rw [Marked.erase_markAt,Marked.erase_mark]
    · intro q; simp [Marked.active_markAt,Marked.active_mark]
  have endShape := localHistory.skeleton_eq h.tracked initialShape
  have erased : slice.erase=h.markedTarget.passive.erase := by
    simpa only [Marked.skeleton_erase] using congrArg Marked.erase endShape
  have localTrace : Marked.tracePositions (pre++r) slice=
      Marked.tracePositions r h.markedTarget.passive := by
    apply Marked.trace_eq_of_members erased
    intro q
    rw [Marked.subtreeAt_trace lookup]
    exact global.prefix_trace_iff h.tracked hp
  have entire : Marked.tracePositions (pre++r) H.markedTarget.passive=
      (Marked.tracePositions (pre++r) slice).map (fun q => pre++q) := by
    apply Marked.subtree_trace_eq lookup (Marked.passive_idempotent _)
    intro z hz
    apply H.residualSet_has_prefix paths
    simpa only [ParallelStep.residualSet,Marked.setResidualPositions,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,Marked.passive_trace] using hz
  simpa only [Marked.passive_trace,localTrace] using entire

/-- Context lifting preserves the literal residual list, including ordering
and repetitions induced by arbitrary invalid or repeated old selection names. -/
theorem ParallelStep.residualSet_prefix_eq (h : ParallelStep F a b) (H : ParallelStep K t u)
    (hp : subtermAt t pre=some a)
    (paths : H.paths=h.paths.map (fun q => pre++q)) (names : List Path) :
    H.residualSet (names.map (fun q => pre++q))=
      (h.residualSet names).map (fun q => pre++q) := by
  induction names with
  | nil => rfl
  | cons r rs ih =>
    change Marked.tracePositions (pre++r) H.markedTarget++
        H.residualSet (rs.map (fun q => pre++q)) =
      (Marked.tracePositions r h.markedTarget++h.residualSet rs).map (fun q => pre++q)
    rw [h.trace_prefix_eq H hp paths r,ih,List.map_append]

end Lamping.Lambda
