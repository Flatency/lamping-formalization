import Lamping.Lambda.TagProjection
import Lamping.Lambda.ContextualHistories
import Lamping.Lambda.ParallelMovesResidual
import Lamping.Lambda.NoTagTransport
namespace Lamping.Lambda.Marked
/-- Actual annotated subtree, exposing a red node's implicit lambda. -/
def childAt : Marked → Lambda.Step → Option Marked
  | .lam b, .body => some b
  | .app _ f _, .fn => some f
  | .app _ _ a, .arg => some a
  | .red _ b _, .fn => some (.lam b)
  | .red _ _ a, .arg => some a
  | _, _ => none

def subtreeAt : Marked → Path → Option Marked
  | t, [] => some t
  | t, e :: p => (childAt t e).bind (fun a => subtreeAt a p)

 theorem childAt_erase (hp : childAt t e = some a) :
     Lambda.subtermAt t.erase [e] = some a.erase := by
   cases t <;> cases e <;> simp [childAt] at hp <;> subst a <;> simp [Lambda.subtermAt, erase]
 theorem subtreeAt_erase (hp : subtreeAt t p = some a) :
     Lambda.subtermAt t.erase p = some a.erase := by
   induction p generalizing t with
   | nil => cases hp; simp [Lambda.subtermAt]
   | cons e p ih =>
     cases hc : childAt t e with
     | none => simp [subtreeAt, hc] at hp
     | some c =>
       have hcp : subtreeAt c p = some a := by simpa [subtreeAt, hc] using hp
       have he := childAt_erase hc
       have hh := ih hcp
       have hl := Lambda.subtermAt_append t.erase [e] p
       simpa [he, hh] using hl

 theorem childAt_tags (hp : childAt t e = some a) (q : Path) :
     tagsAt a q = tagsAt t (e :: q) := by
   cases t <;> cases e <;> simp [childAt] at hp <;> subst a <;>
     try rfl
   cases q with
   | nil => rfl
   | cons e q => cases e <;> rfl
 theorem subtreeAt_tags (hp : subtreeAt t p = some a) (q : Path) :
     tagsAt a q = tagsAt t (p ++ q) := by
   induction p generalizing t with
   | nil => cases hp; rfl
   | cons e p ih =>
     cases hc : childAt t e with
     | none => simp [subtreeAt, hc] at hp
     | some c =>
       have hcp : subtreeAt c p = some a := by simpa [subtreeAt, hc] using hp
       exact (ih hcp).trans (childAt_tags hc (p ++ q))
 theorem subtreeAt_trace (hp : subtreeAt t p = some a) :
     q ∈ tracePositions r a ↔ p ++ q ∈ tracePositions r t := by
   rw [← mem_tagsAt, ← mem_tagsAt, subtreeAt_tags hp]

 theorem ReductionAt.child_lift (hc : childAt t e = some a) (h : ReductionAt q a b) :
     ∃ u, ReductionAt (e :: q) t u ∧ childAt u e = some b := by
   cases t with
   | var => cases e <;> cases hc
   | lam c => cases e with
     | fn => cases hc
     | arg => cases hc
     | body => cases hc; exact ⟨_, .lam h, rfl⟩
   | app l f c => cases e with
     | body => cases hc
     | fn => cases hc; exact ⟨_, .appL h, rfl⟩
     | arg => cases hc; exact ⟨_, .appR h, rfl⟩
   | red l c d => cases e with
     | body => cases hc
     | arg => cases hc; exact ⟨_, .redR h, rfl⟩
     | fn =>
       cases hc
       cases h with
       | lam h => exact ⟨_, .redL h, rfl⟩

 theorem ReductionAt.prefix_lift (hp : subtreeAt t pre = some a) (h : ReductionAt q a b) :
     ∃ u, ReductionAt (pre ++ q) t u ∧ subtreeAt u pre = some b := by
   induction pre generalizing t with
   | nil => cases hp; exact ⟨_, h, rfl⟩
   | cons e pre ih =>
     cases hc : childAt t e with
     | none => simp [subtreeAt, hc] at hp
     | some c =>
       have hcp : subtreeAt c pre = some a := by simpa [subtreeAt, hc] using hp
       obtain ⟨d, hd, hdp⟩ := ih hcp
       obtain ⟨u, hu, hue⟩ := hd.child_lift hc
       exact ⟨u, hu, by simp [subtreeAt, hue, hdp]⟩

 theorem ReductionAt.prefix_reflect (hp : subtreeAt t pre = some a)
     (h : ReductionAt (pre ++ q) t u) :
     ∃ b, ReductionAt q a b ∧ subtreeAt u pre = some b := by
   obtain ⟨b0, hb0, _, _⟩ := h.betaAt.prefix_reflect (subtreeAt_erase hp)
   obtain ⟨b, hb, _⟩ := lift_general_betaAt hb0
   obtain ⟨u', hu', hup⟩ := hb.prefix_lift hp
   have he := h.deterministic hu'
   cases he
   exact ⟨b, hb, hup⟩

 theorem History.prefix_lift (h : History ps a b) (hp : subtreeAt t pre = some a) :
     ∃ u, History (ps.map (fun q => pre ++ q)) t u ∧ subtreeAt u pre = some b := by
   induction h generalizing t with
   | nil => exact ⟨_, .nil _, hp⟩
   | cons h hs ih =>
     obtain ⟨v, hv, hvp⟩ := h.prefix_lift hp
     obtain ⟨u, hu, hup⟩ := ih hvp
     exact ⟨u, .cons hv hu, hup⟩

 theorem History.prefix_reflect (h : History (ps.map (fun q => pre ++ q)) t u)
     (hp : subtreeAt t pre = some a) :
     ∃ b, History ps a b ∧ subtreeAt u pre = some b := by
   induction ps generalizing t a with
   | nil => cases h; exact ⟨_, .nil _, hp⟩
   | cons q ps ih =>
     cases h with
     | cons h hs =>
       obtain ⟨b, hb, hbp⟩ := h.prefix_reflect hp
       obtain ⟨c, hc, hcp⟩ := ih hs hbp
       exact ⟨c, .cons hb hc, hcp⟩

 theorem childAt_markAt (hp : Lambda.subtermAt t [e] = some a) (seed : Path) :
     childAt (markAt [] t seed) e = some (markAt [] a (seed ++ [e])) := by
   cases t with
   | var i => cases e <;> cases hp
   | lam b => cases e with
     | fn => cases hp
     | arg => cases hp
     | body => simp only [Lambda.subtermAt, Option.some.injEq] at hp; subst a; rfl
   | app f b => cases e with
     | body => cases hp
     | fn =>
       simp only [Lambda.subtermAt, Option.some.injEq] at hp; subst a
       cases f <;> simp [markAt, childAt, List.append_assoc]
     | arg =>
       simp only [Lambda.subtermAt, Option.some.injEq] at hp; subst a
       cases f <;> simp [markAt, childAt]

 theorem subtreeAt_markAt (hp : Lambda.subtermAt t pre = some a) (seed : Path) :
     subtreeAt (markAt [] t seed) pre = some (markAt [] a (seed ++ pre)) := by
   induction pre generalizing t seed with
   | nil => simp only [Lambda.subtermAt, Option.some.injEq] at hp; subst a; simp [subtreeAt]
   | cons e pre ih =>
     obtain ⟨c, hc, hcp⟩ := Lambda.prefix_exists (p := [e]) (q := pre) hp
     have hh := ih hcp (seed ++ [e])
     simpa [subtreeAt, childAt_markAt hc, List.append_assoc] using hh

 theorem History.tagsAt_outside_prefix {ps : List Path} (h : History (ps.map (fun p => pre ++ p)) t u)
     (hn : ¬ ∃ tail, q = pre ++ tail) : tagsAt u q = tagsAt t q := by
   induction ps generalizing t with
   | nil => cases h; rfl
   | cons p ps ih =>
     cases h with
     | cons h hs =>
       have he := h.tagsAt_outside (by
         rintro ⟨tail, he⟩
         exact hn ⟨p ++ tail, by simpa only [List.append_assoc] using he⟩)
       exact (ih hs).trans he

 theorem History.trace_fixed_outside {ps : List Path} (h : History (ps.map (fun p => pre ++ p)) t u)
     (hn : ∀ tail, pre ++ tail ∉ tracePositions r t) :
     tracePositions r u = tracePositions r t := by
   induction ps generalizing t with
   | nil => cases h; rfl
   | cons p ps ih =>
     cases h with
     | cons h hs =>
       have he := h.trace_outside (by intro tail ht; exact hn (p ++ tail) (by simpa only [List.append_assoc] using ht))
       exact (ih hs (by intro tail ht; rw [he] at ht; exact hn tail ht)).trans he

 theorem History.prefix_trace_iff
     (h : History (ps.map (fun p => pre ++ p)) (mark [] t) u)
     (k : History ps (mark [] a) b) (hp : Lambda.subtermAt t pre = some a) :
     pre ++ q ∈ tracePositions (pre ++ r) u ↔ q ∈ tracePositions r b := by
   have hinit : subtreeAt (mark [] t) pre = some (markAt [] a pre) := by
     simpa only [mark, List.nil_append] using subtreeAt_markAt hp []
   obtain ⟨slice, hs, hlookup⟩ := h.prefix_reflect hinit
   have initial (z : Path) : z ∈ tracePositions r (mark [] a) ↔
       z ∈ tracePositions (pre ++ r) (markAt [] a pre) := by
     rw [trace_mark, trace_markAt]
     constructor
     · rintro ⟨hz, hred⟩; exact ⟨congrArg (pre ++ ·) hz, hred⟩
     · rintro ⟨hz, hred⟩; exact ⟨List.append_cancel_left hz, hred⟩
   have fwd := k.trace_inclusion hs (by simp only [erase_mark, erase_markAt]) (fun z => (initial z).mp)
   have back := hs.trace_inclusion k (by simp only [erase_mark, erase_markAt]) (fun z => (initial z).mpr)
   rw [← subtreeAt_trace hlookup]
   exact ⟨back q, fwd q⟩
end Lamping.Lambda.Marked

namespace Lamping.Lambda

 theorem ParallelStep.residualSet_prefix_iff (h : ParallelStep F t u) (k : ParallelStep G a b)
     (hp : subtermAt t pre = some a) (paths : h.paths = k.paths.map (fun p => pre ++ p)) :
     pre ++ q ∈ h.residualSet [pre ++ r] ↔ q ∈ k.residualSet [r] := by
   have hh : Marked.History (k.paths.map (fun p => pre ++ p)) (Marked.mark [] t) h.markedTarget.passive := by
     simpa only [paths] using h.tracked
   have he := hh.prefix_trace_iff k.tracked hp (q := q) (r := r)
   simpa only [Marked.passive_trace, ParallelStep.residualSet, Marked.setResidualPositions,
     List.flatMap_cons, List.flatMap_nil, List.append_nil] using he

 theorem ParallelStep.residualSet_has_prefix {ps : List Path} (h : ParallelStep F t u)
     (paths : h.paths = ps.map (fun p => pre ++ p))
     (hz : z ∈ h.residualSet [pre ++ r]) : ∃ q, z = pre ++ q := by
   apply Classical.byContradiction
   intro hn
   have hh : Marked.History (ps.map (fun p => pre ++ p)) (Marked.mark [] t) h.markedTarget.passive := by
     simpa only [paths] using h.tracked
   have ht : z ∈ Marked.tracePositions (pre ++ r) h.markedTarget.passive := by
     simpa only [Marked.passive_trace, ParallelStep.residualSet, Marked.setResidualPositions,
       List.flatMap_cons, List.flatMap_nil, List.append_nil] using hz
   have tag := (Marked.mem_tagsAt _ (pre ++ r) z).mpr ht
   rw [hh.tagsAt_outside_prefix hn] at tag
   have trace := (Marked.mem_tagsAt _ (pre ++ r) z).mp tag
   have he := ((Marked.trace_mark [] t (pre ++ r) z).mp trace).1
   exact hn ⟨r, he.symm⟩

 theorem ParallelStep.residualSet_prefix_members (h : ParallelStep F t u) (k : ParallelStep G a b)
     (hp : subtermAt t pre = some a) (paths : h.paths = k.paths.map (fun p => pre ++ p)) :
     z ∈ h.residualSet [pre ++ r] ↔ z ∈ (k.residualSet [r]).map (fun p => pre ++ p) := by
   constructor
   · intro hz
     obtain ⟨q, hq⟩ := h.residualSet_has_prefix paths hz
     subst z
     exact List.mem_map.mpr ⟨q, (h.residualSet_prefix_iff k hp paths).mp hz, rfl⟩
   · intro hz
     obtain ⟨q, hq, he⟩ := List.mem_map.mp hz
     subst z
     exact (h.residualSet_prefix_iff k hp paths).mpr hq

/-- Residuals in a fixed context are exactly the local residuals, with both
 initial and final positions prefixed. The proof keeps the global old names
 in the sliced annotated history and compares them to fresh local names. -/
 theorem Derivation.prefix_residual_iff (h : Derivation a b) (H : Derivation t u)
     (hp : subtermAt t pre = some a)
     (paths : H.paths = h.paths.map (fun q => pre ++ q))
     (r : RedexOcc a) (s : RedexOcc b) (R : RedexOcc t) (S : RedexOcc u)
     (hr : R.val = pre ++ r.val) (hs : S.val = pre ++ s.val) :
     H.Residual R S ↔ h.Residual r s := by
   obtain ⟨v, hv, _⟩ := H.tracked
   have hvm : Marked.History (h.paths.map (fun q => pre ++ q)) (Marked.mark [] t) v := by
     simpa only [paths] using hv
   have hinit : Marked.subtreeAt (Marked.mark [] t) pre = some (Marked.markAt [] a pre) := by
     simpa only [Marked.mark, List.nil_append] using Marked.subtreeAt_markAt hp []
   obtain ⟨slice, hlocal, hlookup⟩ := hvm.prefix_reflect hinit
   obtain ⟨fresh, hfresh, _⟩ := h.tracked
   have initial (q : Path) : q ∈ Marked.tracePositions r.val (Marked.mark [] a) ↔
       q ∈ Marked.tracePositions R.val (Marked.markAt [] a pre) := by
     rw [Marked.initial_residual, Marked.trace_markAt]
     constructor
     · intro hq
       subst q
       exact ⟨hr, (mem_redexPositions a r.val).mpr r.property⟩
     · rintro ⟨he, _⟩
       exact (List.append_cancel_left (hr.symm.trans he)).symm
   have incl := hfresh.trace_inclusion hlocal
     (by simp only [Marked.erase_mark, Marked.erase_markAt]) (fun q => (initial q).mp)
   have back := hlocal.trace_inclusion hfresh
     (by simp only [Marked.erase_mark, Marked.erase_markAt]) (fun q => (initial q).mpr)
   rw [Derivation.residual_iff_tracking H hv, Derivation.residual_iff_tracking h hfresh, hs]
   rw [← Marked.subtreeAt_trace hlookup]
   exact ⟨back s.val, incl s.val⟩

 theorem Derivation.prefix_residual_outside_target {ps : List Path} (h : Derivation t u)
     (paths : h.paths = ps.map (fun p => pre ++ p)) (r : RedexOcc t) (s : RedexOcc u)
     (hn : ¬ ∃ tail, s.val = pre ++ tail) (hr : h.Residual r s) : r.val = s.val := by
   obtain ⟨v, hv, _, htrace⟩ := hr
   have hh : Marked.History (ps.map (fun p => pre ++ p)) (Marked.mark [] t) v := by
     simpa only [paths] using hv
   have htag := (Marked.mem_tagsAt _ r.val s.val).mpr htrace
   rw [hh.tagsAt_outside_prefix hn] at htag
   have hi := (Marked.mem_tagsAt _ r.val s.val).mp htag
   exact ((Marked.initial_residual [] t r s.val).mp hi).symm

 theorem Derivation.prefix_residual_outside_source {ps : List Path} (h : Derivation t u)
     (paths : h.paths = ps.map (fun p => pre ++ p)) (r : RedexOcc t) (s : RedexOcc u)
     (hn : ¬ ∃ tail, r.val = pre ++ tail) (hr : h.Residual r s) : r.val = s.val := by
   obtain ⟨v, hv, _, htrace⟩ := hr
   have hh : Marked.History (ps.map (fun p => pre ++ p)) (Marked.mark [] t) v := by
     simpa only [paths] using hv
   have he := hh.trace_fixed_outside (r := r.val) (by
     intro tail ht
     exact hn ⟨tail, ((Marked.initial_residual [] t r (pre ++ tail)).mp ht).symm⟩)
   rw [he] at htrace
   exact ((Marked.initial_residual [] t r s.val).mp htrace).symm
end Lamping.Lambda

