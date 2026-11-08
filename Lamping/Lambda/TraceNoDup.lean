import Lamping.Lambda.ResidualInit
namespace Lamping.Lambda.Marked

private theorem cons_map_nodup (e : Lambda.Step) (ps : List Path) (h : ps.Nodup) :
    (ps.map (e :: ·)).Nodup := by
  exact List.Pairwise.map _ (fun _ _ hn he => hn (List.cons.inj he).2) h

private theorem fork_nodup (ps qs : List Path) (hp : ps.Nodup) (hq : qs.Nodup) :
    (ps.map (.fn :: ·) ++ qs.map (.arg :: ·)).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨cons_map_nodup _ _ hp,cons_map_nodup _ _ hq,?_⟩
  intro a ha b hb he
  obtain ⟨x,_,hx⟩ := List.mem_map.mp ha
  obtain ⟨y,_,hy⟩ := List.mem_map.mp hb
  cases hx.trans (he.trans hy.symm)

private theorem root_fork_nodup (ps qs : List Path) (hp : ps.Nodup) (hq : qs.Nodup) :
    ([] :: (ps.map (.fn :: ·) ++ qs.map (.arg :: ·))).Nodup := by
  apply List.nodup_cons.mpr
  exact ⟨by simp,fork_nodup ps qs hp hq⟩

/-- Occurrence paths in the trace of a fixed old name never repeat, even
with arbitrary annotation lists, repeated names, or active bits. -/
theorem tracePositions_nodup (r : Path) (t : Marked) : (tracePositions r t).Nodup := by
  induction t with
  | var => exact .nil
  | lam b ih => exact cons_map_nodup _ _ ih
  | app l f a hf ha =>
    by_cases h : r∈l
    · simpa only [tracePositions,if_pos h,List.singleton_append] using root_fork_nodup _ _ hf ha
    · simpa only [tracePositions,if_neg h,List.nil_append] using fork_nodup _ _ hf ha
  | red l b a hb ha =>
    have hbody := cons_map_nodup .body _ hb
    by_cases h : r∈l
    · simpa only [tracePositions,if_pos h,List.singleton_append,List.map_map,Function.comp_def] using
        root_fork_nodup _ _ hbody ha
    · simpa only [tracePositions,if_neg h,List.nil_append,List.map_map,Function.comp_def] using
        fork_nodup _ _ hbody ha

private theorem singleton_of_nodup_members {ps : List Path} (h : ps.Nodup)
    (members : ∀ q, q∈ps ↔ q=p) : ps=[p] := by
  cases ps with
  | nil => have := (members p).mpr rfl; cases this
  | cons a tail =>
    have ha : a=p := (members a).mp (by simp)
    subst a
    have empty : tail=[] := by
      cases tail with
      | nil => rfl
      | cons b rest =>
        have hb : b=p := (members b).mp (by simp)
        exact False.elim ((List.nodup_cons.mp h).1 (by simp [hb]))
    rw [empty]

/-- Extensional singleton membership determines the literal trace list,
because the occurrence tree already excludes duplicate paths. -/
theorem trace_singleton_of_members (r p : Path) (t : Marked)
    (members : ∀ q, q∈tracePositions r t ↔ q=p) : tracePositions r t=[p] :=
  singleton_of_nodup_members (tracePositions_nodup _ _) members

/-- Initializing an actual source redex gives literally one occurrence,
not merely equality of membership predicates. -/
theorem initial_trace_singleton (F : List Path) (t : Term) (r : RedexOcc t) :
    tracePositions r.val (mark F t)=[r.val] := by
  apply singleton_of_nodup_members (tracePositions_nodup _ _)
  intro q
  rw [trace_mark]
  constructor
  · intro h; exact h.1.symm
  · intro he; subst q; exact ⟨rfl,(mem_redexPositions t r.val).mpr r.property⟩

theorem initial_trace_singleton_at (F : List Path) (t : Term) (pre : Path) (r : RedexOcc t) :
    tracePositions (pre++r.val) (markAt F t pre)=[r.val] := by
  apply singleton_of_nodup_members (tracePositions_nodup _ _)
  intro q
  rw [trace_markAt]
  constructor
  · intro h; exact (List.append_cancel_left h.1).symm
  · intro he; subst q; exact ⟨rfl,(mem_redexPositions t r.val).mpr r.property⟩

end Lamping.Lambda.Marked
