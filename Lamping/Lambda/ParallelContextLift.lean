import Lamping.Lambda.ParallelPrefixScope
namespace Lamping.Lambda
namespace SyntaxFrame

private def annotated (C : SyntaxFrame) (t : Marked) : Marked :=
  match C with
  | .fn a => .app [] t (Marked.mark [] a)
  | .arg f => .app [] (Marked.mark [] f) t
  | .body => .lam t

private theorem annotated_erase (C : SyntaxFrame) (t : Marked) :
    (C.annotated t).erase=C.plug t.erase := by
  cases C <;> simp [annotated,plug,Marked.erase,Marked.erase_mark]

private theorem annotated_normal (C : SyntaxFrame) (h : Marked.Normal t) :
    Marked.Normal (C.annotated t) := by
  have hn (a : Term) : Marked.Normal (Marked.mark [] a) :=
    Marked.normal_markAt_no_selection (by simp)
  cases C with
  | fn a => exact ⟨h,hn a⟩
  | arg f => exact ⟨hn f,h⟩
  | body => exact h

private theorem annotated_history (C : SyntaxFrame)
    (h : Marked.RelativeHistory ps t u) :
    Marked.RelativeHistory (ps.map (C.edge::·)) (C.annotated t) (C.annotated u) := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih =>
    apply Marked.RelativeHistory.cons ?_ ih
    cases C with
    | fn a => exact .appL h
    | arg f => exact .appR h
    | body => exact .lam h

/-- Lift the chosen complete schedule, retaining passive names by skeleton
transport from the real global initial marking. -/
theorem parallel_lift (C : SyntaxFrame) (h : ParallelStep F a b) :
    ∃ k : ParallelStep (F.map (C.edge::·)) (C.plug a) (C.plug b),
      k.paths=h.paths.map (C.edge::·) := by
  have hh := (Marked.completeOld_iff F a).mp h.complete
  have shape : (C.annotated (Marked.mark F a)).skeleton =
      (Marked.mark (F.map (C.edge::·)) (C.plug a)).skeleton := by
    apply Marked.skeleton_of_shape
    · rw [annotated_erase,Marked.erase_mark,Marked.erase_mark]
    · intro q
      have empty (t : Term) : Marked.activePositions (Marked.mark [] t)=[] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro p hp
        simp [Marked.active_mark] at hp
      cases C <;> cases q with
      | nil => simp [annotated,edge,plug,Marked.activePositions,empty,Marked.active_mark]
      | cons e q =>
        cases e <;> simp [annotated,edge,plug,Marked.activePositions,empty,Marked.active_mark,
          mem_redexPositions,subtermAt]
  obtain ⟨v,hv,vs⟩ := (C.annotated_history hh.1).lift_skeleton shape
  have vn := Marked.normal_of_skeleton vs (C.annotated_normal hh.2)
  have ve : v.erase=C.plug b := by
    have same := congrArg Marked.erase vs
    rw [Marked.skeleton_erase,Marked.skeleton_erase,annotated_erase,h.target_eq] at same
    exact same.symm
  exact ⟨⟨h.paths.map (C.edge::·),v,(Marked.completeOld_iff _ _).mpr ⟨hv,vn⟩,ve⟩,rfl⟩

end SyntaxFrame

/-- Put a given complete development into an arbitrary existing subtree.
The schedule is exactly the chosen local schedule with the context prefix. -/
theorem ParallelStep.prefix_lift (h : ParallelStep F a b)
    (hp : subtermAt t pre=some a) :
    ∃ u, ∃ k : ParallelStep (F.map (fun q => pre++q)) t u,
      subtermAt u pre=some b ∧ k.paths=h.paths.map (fun q => pre++q) := by
  induction pre generalizing t with
  | nil =>
    simp only [subtermAt,Option.some.injEq] at hp
    subst t
    let k := h.reindex (F.map (fun q => []++q)) (fun q => by simp)
    exact ⟨b,k,by cases b <;> rfl,by simp [k,ParallelStep.reindex]⟩
  | cons e pre ih =>
    have frame (C : SyntaxFrame) (c : Term)
        (hp : subtermAt (C.plug c) (C.edge::pre)=some a) :
        ∃ u, ∃ k : ParallelStep (F.map (fun q => (C.edge::pre)++q)) (C.plug c) u,
          subtermAt u (C.edge::pre)=some b ∧
          k.paths=h.paths.map (fun q => (C.edge::pre)++q) := by
      have localLookup : subtermAt c pre=some a := by
        change subtermAt (C.plug c) ([C.edge]++pre)=some a at hp
        simpa only [subtermAt_append,C.lookup,Option.bind_some] using hp
      obtain ⟨d,k,lookup,paths⟩ := ih localLookup
      obtain ⟨j,jpaths⟩ := C.parallel_lift k
      let global := j.reindex (F.map (fun q => (C.edge::pre)++q))
        (fun q => by simp only [List.map_map,Function.comp_def,List.cons_append])
      refine ⟨C.plug d,global,?_,?_⟩
      · change subtermAt (C.plug d) ([C.edge]++pre)=some b
        rw [subtermAt_append,C.lookup,Option.bind_some,lookup]
      · change j.paths=h.paths.map (fun q => (C.edge::pre)++q)
        rw [jpaths,paths]
        simp only [List.map_map,Function.comp_def,List.cons_append]
    cases t with
    | var i => cases e <;> simp [subtermAt] at hp
    | lam c =>
      cases e with
      | body => exact frame .body c hp
      | fn => simp [subtermAt] at hp
      | arg => simp [subtermAt] at hp
    | app f c =>
      cases e with
      | fn => exact frame (.fn c) f hp
      | arg => exact frame (.arg f) c hp
      | body => simp [subtermAt] at hp
end Lamping.Lambda
