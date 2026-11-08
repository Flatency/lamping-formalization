import Lamping.Lambda.ParallelMovesResidual
namespace Lamping.Lambda

theorem Derivation.tracking_erase (h : Derivation t u)
    (tracking : Marked.History h.paths annotations target) (source : annotations.erase=t) :
    target.erase=u := by
  obtain ⟨other,history,finish⟩ := Marked.lift_betaHistory h.valid annotations source
  have same := tracking.deterministic history
  subst other
  exact finish

/-- Both stages of a genuine residual square together form a complete
development of the union, retaining their exact chosen path sequences. -/
theorem ParallelStep.composite_relative_union (h : ParallelStep F t u)
    (k : ParallelStep (h.residualSet G) u v) :
    Marked.RelativeHistory (h.derivation.append k.derivation).paths (Marked.mark (F++G) t)
      (Marked.dev (Marked.reselect G h.markedTarget)) := by
  have hF := (Marked.completeOld_iff F t).mp h.complete
  have first := hF.1.reselect_mono (Marked.valid_mark F t) (Marked.selected_mark F t)
    (G:=F++G) (fun r hr => List.mem_append_left G hr)
  rw [Marked.reselect_mark] at first
  have selected := hF.1.general.selected (Marked.selected_mark F t)
  rw [Marked.reselect_union_of_complete selected hF.2] at first
  have kG := (Marked.completeOld_iff (h.residualSet G) u).mp k.complete
  obtain ⟨w,second,shape⟩ := kG.1.lift_skeleton (h.residual_skeleton G).symm
  have normal := Marked.normal_of_skeleton shape kG.2
  have eq : w=Marked.dev (Marked.reselect G h.markedTarget) :=
    Marked.complete_unique ⟨second.steps,normal⟩ ⟨Marked.steps_to_dev _,Marked.normal_dev _⟩
  subst w
  exact first.append second

theorem marked_union_comm (F G : List Path) (t : Term) :
    Marked.mark (F++G) t=Marked.mark (G++F) t := by
  rw [←Marked.reselect_mark (F++G) [] t,←Marked.reselect_mark (G++F) [] t]
  exact Marked.reselect_append_comm _ (Marked.valid_mark [] t)

/-- The actual two paths of any residual square agree when tracking
arbitrary annotations on the union's source skeleton. In particular old
application identities may annotate nonredexes: Valid is not an input. -/
theorem ParallelMovesSquare.tracking_diamond
    (sq : ParallelMovesSquare F G t u v w) (annotations : Marked)
    (shape : (Marked.mark (F++G) t).skeleton=annotations.skeleton) :
    ∃ target : Marked,
      Marked.History (sq.first.derivation.append sq.afterFirst.derivation).paths annotations target ∧
      Marked.History (sq.second.derivation.append sq.afterSecond.derivation).paths annotations target := by
  have left := sq.first.composite_relative_union sq.afterFirst
  have right := sq.second.composite_relative_union sq.afterSecond
  rw [←marked_union_comm F G t] at right
  obtain ⟨l,hl,shapeL⟩ := left.lift_skeleton shape
  obtain ⟨r,hr,shapeR⟩ := right.lift_skeleton shape
  have normalL := Marked.normal_of_skeleton shapeL (Marked.normal_dev _)
  have normalR := Marked.normal_of_skeleton shapeR (Marked.normal_dev _)
  have eq : l=r := Marked.complete_unique ⟨hl.steps,normalL⟩ ⟨hr.steps,normalR⟩
  subst r
  exact ⟨l,hl.general,hr.general⟩
end Lamping.Lambda
