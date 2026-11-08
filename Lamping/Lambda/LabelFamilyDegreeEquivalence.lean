import Lamping.Lambda.LabelCanonicalDegreeUniqueness
import Lamping.Lambda.CanonicalUniqueness
namespace Lamping.Lambda.Labelled

/-- Canonical pointed representatives are equal when their degrees agree
in one arbitrary original INIT labelling. Actual history lifts supply all
labels; representation uniqueness concerns the original historical points. -/
theorem canonical_point_degree_unique (t : LTerm) (initial : INIT t)
    (a b : RedexWithHistory t.erase) (run other : ExtractionRun t.erase)
    (canonical : CanonicalRun run) (canonical' : CanonicalRun other)
    (represented : RunRepresents run a) (represented' : RunRepresents other b)
    (same : degreeAlong t a.history.derivation.paths a.redex.val=
      degreeAlong t b.history.derivation.paths b.redex.val) : a=b := by
  rcases a with ⟨target,program,redex⟩
  rcases b with ⟨target',program',redex'⟩
  obtain ⟨u,history,erased⟩ := lift_history program.derivation.valid t rfl
  obtain ⟨u',history',erased'⟩ := lift_history program'.derivation.valid t rfl
  cases erased
  cases erased'
  obtain ⟨last,ordinary,shape⟩ := represented
  obtain ⟨last',ordinary',shape'⟩ := represented'
  obtain ⟨final,atLast,_⟩ := lift_betaAt (t := u) last
  obtain ⟨final',atLast',_⟩ := lift_betaAt (t := u') last'
  obtain ⟨l,degree⟩ := degreeAt_exists u redex
  have degree' : u'.degreeAt redex'.val=some l := by
    rw [degreeAlong_witness history,degreeAlong_witness history'] at same
    exact same.symm.trans degree
  have paths : run.history.derivation.paths=program.derivation.paths++[redex.val] := by
    rw [shape,ParallelHistory.derivation_append]
    rfl
  have paths' : other.history.derivation.paths=program'.derivation.paths++[redex'.val] := by
    rw [shape',ParallelHistory.derivation_append]
    rfl
  have runEqual := history.canonical_degree_runs_unique atLast history' atLast' initial run other canonical canonical'
    paths paths' degree degree'
  have originalRep : RunRepresents run ⟨u.erase,program,redex⟩ := ⟨last,ordinary,shape⟩
  have originalRep' : RunRepresents other ⟨u'.erase,program',redex'⟩ := ⟨last',ordinary',shape'⟩
  rw [runEqual] at originalRep
  exact originalRep.unique originalRep'

/-- AG6.2.10, for arbitrary actual historical redexes and every common
original INIT labelling. FamilyEq is the frozen historical Copy closure;
it is not defined using degrees, and INIT is never imposed on reducts. -/
theorem family_iff_degree (t : LTerm) (initial : INIT t) (a b : RedexWithHistory t.erase) :
    FamilyEq a b ↔ degreeAlong t a.history.derivation.paths a.redex.val=
      degreeAlong t b.history.derivation.paths b.redex.val := by
  constructor
  · intro family
    exact Labelled.FamilyEq.degreeAlong family t rfl
  · intro same
    obtain ⟨run,left,canonical,represented,leftFamily⟩ := a.canonical_exists
    obtain ⟨other,right,canonical',represented',rightFamily⟩ := b.canonical_exists
    have leftTransport := Labelled.FamilyEq.degreeAlong leftFamily t rfl
    have rightTransport := Labelled.FamilyEq.degreeAlong rightFamily t rfl
    have degreeEqual := leftTransport.symm.trans (same.trans rightTransport)
    have pointsEqual := canonical_point_degree_unique t initial left right run other canonical canonical' represented represented' degreeEqual
    cases pointsEqual
    exact leftFamily.trans rightFamily.symm

/-- The arbitrary unlabelled source formulation preserves the complete
quantifier over all original INIT assignments erasing to that source. -/
theorem family_iff_degree_of_erase (a b : RedexWithHistory m) (t : LTerm)
    (initial : INIT t) (source : t.erase=m) :
    FamilyEq a b ↔ degreeAlong t a.history.derivation.paths a.redex.val=
      degreeAlong t b.history.derivation.paths b.redex.val := by
  cases source
  exact family_iff_degree t initial a b
end Lamping.Lambda.Labelled
