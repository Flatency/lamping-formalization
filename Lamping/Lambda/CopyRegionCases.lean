import Lamping.Lambda.CopyArgumentProjection
import Lamping.Lambda.CopyLeftExtraction
namespace Lamping.Lambda

theorem LeftOf.inside_or_disjoint (before : LeftOf p q) :
    (∃s,q=p++s) ∨ DisjointPositions p q := by
  induction before with
  | outer e q => exact .inl ⟨e::q,rfl⟩
  | child e before ih =>
    rcases ih with ⟨s,eq⟩ | apart
    · exact .inl ⟨s,congrArg (e::·) eq⟩
    · exact .inr (apart.cons e)
  | branch p q => exact .inr (DisjointPositions.head_ne (by intro eq; cases eq))

/-- Real redex positions strictly after a protected real redex occupy its
function, its argument, or a disjoint subtree. The invalid body port of an
application is excluded by actual subterm lookups. -/
theorem RedexOcc.after_regions (cut target : RedexOcc t) (before : LeftOf cut.val target.val) :
    (∃q,target.val=(cut.val++[.fn])++q) ∨
    (∃q,target.val=(cut.val++[.arg])++q) ∨ DisjointPositions cut.val target.val := by
  rcases before.inside_or_disjoint with ⟨suffix,eq⟩ | apart
  · cases suffix with
    | nil => exact False.elim (LeftOf.irrefl cut.val (by simpa only [eq,List.append_nil] using before))
    | cons e suffix =>
      cases e with
      | fn => exact .inl ⟨suffix,by simpa only [List.append_assoc,List.singleton_append] using eq⟩
      | arg => exact .inr (.inl ⟨suffix,by simpa only [List.append_assoc,List.singleton_append] using eq⟩)
      | body =>
        obtain ⟨cutTerm,lookup,redex⟩ := cut.property
        obtain ⟨targetTerm,targetLookup,_⟩ := target.property
        rw [eq,subtermAt_append,lookup] at targetLookup
        cases cutTerm with
        | var => cases redex
        | lam => cases redex
        | app f a => cases f <;> simp [IsRedex,subtermAt] at redex targetLookup
  · exact .inr (.inr apart)

end Lamping.Lambda

