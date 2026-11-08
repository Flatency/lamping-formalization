import Lamping.Lambda.LabelRegionalOrigins
import Lamping.Lambda.StandardizationExistence
namespace Lamping.Lambda.Labelled

/-- The finite original redex candidates whose atomic degree occurs in the
transported degree. Edge orientation does not affect atomic membership. -/
def degreeCandidates (t : LTerm) (l : Label) : List Path :=
  (redexPositions t.erase).filter (fun p => match t.degreeAt p with
    | some (.single (.atom n)) => l.edgeWord.any (fun e => e.atom==n)
    | _ => false)

theorem mem_degreeCandidates (t : LTerm) (l : Label) (p : Path) :
    p∈degreeCandidates t l ↔ p∈redexPositions t.erase ∧
      ∃ n,t.degreeAt p=some (Label.atom n) ∧ ∃ e∈l.edgeWord,e.atom=n := by
  simp only [degreeCandidates,List.mem_filter]
  constructor
  · rintro ⟨valid,used⟩
    refine ⟨valid,?_⟩
    cases hd : t.degreeAt p with
    | none => simp [hd] at used
    | some a =>
      cases a with
      | cons => simp [hd] at used
      | single letter =>
        cases letter with
        | over => simp [hd] at used
        | under => simp [hd] at used
        | atom n =>
          refine ⟨n,rfl,?_⟩
          simpa only [hd,List.any_eq_true,beq_iff_eq] using used
  · rintro ⟨valid,n,hd,member⟩
    refine ⟨valid,?_⟩
    simpa only [hd,Label.atom,List.any_eq_true,beq_iff_eq] using member

/-- A real LO source candidate exists for every actual generated degree.
This is candidate existence, not yet the canonical First Redex equality. -/
theorem History.degree_candidate_exists (history : History ps t u) (initial : INIT t)
    (degree : u.degreeAt p=some l) :
    ∃ r : RedexOcc t.erase,LeftmostSelected (degreeCandidates t l) r := by
  obtain ⟨r,n,atInitial,e,member,equal⟩ := history.redex_uses_initial_degree initial degree
  apply leftmost_actual_selected_exists
  exact ⟨r,(mem_degreeCandidates t l r.val).mpr
    ⟨(mem_redexPositions t.erase r.val).mpr r.property,n,atInitial,e,member,equal⟩⟩

theorem degree_candidate_unique (t : LTerm) (l : Label) (r s : RedexOcc t.erase)
    (left : LeftmostSelected (degreeCandidates t l) r)
    (right : LeftmostSelected (degreeCandidates t l) s) : r=s := by
  rcases r.compare s with equal | before | after
  · exact equal
  · exact False.elim (right.2 r left.1 before)
  · exact False.elim (left.2 s right.1 after)
end Lamping.Lambda.Labelled
