import Lamping.Lambda.RootResidualPaths
namespace Lamping.Lambda.Marked
private theorem list_empty_of_no_mem {xs : List α} (h : ∀ q, q ∉ xs) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons q qs => exact False.elim (h q (List.mem_cons_self))
/-- A contraction cannot move an old name which occurs wholly outside its
 contracted subtree. The hypothesis concerns actual source old-name traces. -/
 theorem ReductionAt.trace_outside (h : ReductionAt p t u)
     (hn : ∀ tail, p ++ tail ∉ tracePositions r t) :
     tracePositions r u = tracePositions r t := by
   induction h with
   | appRoot l b a =>
     have hs : tracePositions r (.app l (.lam b) a) = [] :=
       list_empty_of_no_mem hn
     rw [hs]
     apply list_empty_of_no_mem
     intro q hq
     rw [contract_trace_iff] at hq
     rcases hq with hb | ⟨site, tail, _, he, ha⟩
     · apply hn (.fn :: .body :: q)
       simp [tracePositions, hb]
     · apply hn (.arg :: tail)
       simp [tracePositions, ha]
   | redRoot l b a =>
     have hs : tracePositions r (.red l b a) = [] :=
       list_empty_of_no_mem hn
     rw [hs]
     apply list_empty_of_no_mem
     intro q hq
     rw [contract_trace_iff] at hq
     rcases hq with hb | ⟨site, tail, _, he, ha⟩
     · apply hn (.fn :: .body :: q)
       simp [tracePositions, hb]
     · apply hn (.arg :: tail)
       simp [tracePositions, ha]
   | lam h ih =>
     have hh := ih (by intro tail ht; apply hn tail; simpa [tracePositions] using ht)
     simp only [tracePositions, hh]
   | appL h ih =>
     have hh := ih (by intro tail ht; apply hn tail; simp [tracePositions, ht])
     simp only [tracePositions, hh]
   | appR h ih =>
     have hh := ih (by intro tail ht; apply hn tail; simp [tracePositions, ht])
     simp only [tracePositions, hh]
   | redL h ih =>
     have hh := ih (by intro tail ht; apply hn tail; simp [tracePositions, ht])
     simp only [tracePositions, hh]
   | redR h ih =>
     have hh := ih (by intro tail ht; apply hn tail; simp [tracePositions, ht])
     simp only [tracePositions, hh]
end Lamping.Lambda.Marked

namespace Lamping.Lambda
/-- A disjoint initial occurrence has exactly one residual at the same path;
 no copy of that old name can enter the contracted subtree. -/
 theorem BetaAt.disjoint_residual_iff (h : BetaAt t p u) (r : RedexOcc t)
     (hd : DisjointPositions p r.val) (s : RedexOcc u) :
     (singleContraction h).derivation.Residual r s ↔ r.val = s.val := by
   have ht := (singleContraction h).tracked
   change Marked.History [p] (Marked.mark [] t) _ at ht
   cases ht with
   | cons hm hs =>
     cases hs
     have hn : ∀ tail, p ++ tail ∉ Marked.tracePositions r.val (Marked.mark [] t) := by
       intro tail hh
       exact hd.1 ⟨tail, ((Marked.initial_residual [] t r (p ++ tail)).mp hh).symm⟩
     rw [Derivation.residual_iff_tracking _ (.cons hm (.nil _)), hm.trace_outside hn,
       Marked.initial_residual]
     exact eq_comm
 theorem BetaAt.disjoint_residualSet (h : BetaAt t p u) (r : RedexOcc t)
     (hd : DisjointPositions p r.val) (q : Path) :
     q ∈ (singleContraction h).residualSet [r.val] ↔ q = r.val := by
   have ht := (singleContraction h).tracked
   change Marked.History [p] (Marked.mark [] t) _ at ht
   cases ht with
   | cons hm hs =>
     cases hs
     have hn : ∀ tail, p ++ tail ∉ Marked.tracePositions r.val (Marked.mark [] t) := by
       intro tail hh
       exact hd.1 ⟨tail, ((Marked.initial_residual [] t r (p ++ tail)).mp hh).symm⟩
     have he := hm.trace_outside hn
     rw [Marked.passive_trace] at he
     change q ∈ Marked.setResidualPositions [r.val] _ ↔ _
     simp only [Marked.setResidualPositions, List.flatMap_cons, List.flatMap_nil, List.append_nil]
     rw [he, Marked.initial_residual]
end Lamping.Lambda




