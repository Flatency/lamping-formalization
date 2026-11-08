import Lamping.Lambda.LabelArgumentDegreeInterior
namespace Lamping.Lambda.Labelled

/-- If a function-child occurrence is in a region, its parent application
is internal unless that child is exactly the region root. -/
theorem Path.fn_parent_region {p site suffix : Path} (equal : p++[.fn]=site++suffix) :
    (∃ rest,p=site++rest) ∨ p++[.fn]=site := by
  induction site generalizing p suffix with
  | nil => exact .inl ⟨p,rfl⟩
  | cons edge site ih =>
    cases p with
    | nil =>
      have lengths := congrArg List.length equal
      simp only [List.length_append,List.length_cons,List.length_nil] at lengths
      have empty : suffix=[] := List.length_eq_zero_iff.mp (by omega)
      exact .inr (by simpa only [empty,List.append_nil] using equal)
    | cons step p =>
      have heads := (List.cons.inj equal).1
      have tails := (List.cons.inj equal).2
      cases heads
      rcases ih tails with ⟨rest,inside⟩ | boundary
      · exact .inl ⟨rest,congrArg (edge::·) inside⟩
      · exact .inr (congrArg (edge::·) boundary)

/-- A real internal prefix and a next strict regional degree force the next
application occurrence to be internal as well. Root avoidance is reflected
through the actual local history, not an arbitrary RegionCut.here. -/
theorem History.next_strict_degree_internal
    (pre : History ps t u) (initial : INIT t) (atSite : t.subterm site=some subtree)
    (inside : ∀ p∈ps,∃ suffix,p=site++suffix)
    (degree : u.degreeAt p=some l) (support : l.Supported (SourceRegion subtree))
    (rootAvoid : l.Supported (fun n => Label.atom n≠subtree.label)) :
    ∃ suffix,p=site++suffix := by
  obtain ⟨body,atLambda⟩ := LTerm.degreeAt_lambda degree
  have cut := pre.region_cut initial atSite inside
  obtain ⟨suffix,position⟩ := cut.supported_node_internal initial atSite atLambda support
  rcases Path.fn_parent_region position with internal | boundary
  · exact internal
  · have atCurrent : u.subterm site=some (.lam l body) := by rw [←boundary]; exact atLambda
    have oldAvoid := pre.internal_root_support atSite inside atCurrent rootAvoid
    obtain ⟨n,atomic⟩ := initial.1 subtree.label (LTerm.label_mem_of_subterm atSite)
    rw [atomic] at oldAvoid
    exact False.elim (oldAvoid rfl)

/-- Monotone weakening preserves the actual contracted sites and degrees. -/
theorem RegionalHistory.mono (regional : RegionalHistory region ps t u)
    (weaken : ∀ n,region n → larger n) : RegionalHistory larger ps t u := by
  induction regional with
  | nil => exact .nil _
  | cons step degree support rest ih => exact .cons step degree (support.mono weaken) ih

/-- Every actual next contraction obeying the strict colour stays internal.
This is a sufficient-condition bridge with the whole per-event premise
visible; it does not infer those colours from final support or canonicality. -/
theorem RegionalHistory.internal_after_strict_prefix
    (regional : RegionalHistory (fun n => SourceRegion subtree n ∧ Label.atom n≠subtree.label) qs u v)
    (pre : History ps t u) (initial : INIT t) (atSite : t.subterm site=some subtree)
    (inside : ∀ p∈ps,∃ suffix,p=site++suffix) :
    ∀ p∈qs,∃ suffix,p=site++suffix := by
  induction regional generalizing ps with
  | nil => simp
  | @cons p u middle l qs v step degree support rest ih =>
    have firstInside := pre.next_strict_degree_internal initial atSite inside degree
      (support.mono (fun _ member => member.1)) (support.mono (fun _ member => member.2))
    have extended := pre.append (.cons step (.nil _))
    have extendedInside : ∀ q∈ps++[p],∃ suffix,q=site++suffix := by
      intro q member
      rcases List.mem_append.mp member with before | last
      · exact inside q before
      · exact List.mem_singleton.mp last ▸ firstInside
    have tailInside := ih extended extendedInside
    intro q member
    rcases List.mem_cons.mp member with first | later
    · exact first ▸ firstInside
    · exact tailInside q later

/-- Explicit strict regional support at every actual event is sufficient
for a whole internal history from any INIT source and real subtree. -/
theorem RegionalHistory.internal_of_strict_region
    (regional : RegionalHistory (fun n => SourceRegion subtree n ∧ Label.atom n≠subtree.label) ps t u)
    (initial : INIT t) (atSite : t.subterm site=some subtree) :
    ∀ p∈ps,∃ suffix,p=site++suffix := by
  exact regional.internal_after_strict_prefix (.nil t) initial atSite (by simp)
end Lamping.Lambda.Labelled

