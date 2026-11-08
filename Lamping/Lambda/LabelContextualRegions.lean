import Lamping.Lambda.LabelDisjointRegions
namespace Lamping.Lambda.Labelled

/-- Actual source subterms inherit both atomic labels and their nodup order. -/
theorem INIT.subterm (initial : INIT t) (lookup : t.subterm p=some subtree) : INIT subtree := by
  induction p generalizing t with
  | nil =>
    have same : t=subtree := by simpa only [LTerm.subterm,Option.some.injEq] using lookup
    exact same ▸ initial
  | cons step rest ih =>
    cases t with
    | var => cases step <;> simp [LTerm.subterm] at lookup
    | lam l b =>
      cases step with
      | fn => simp [LTerm.subterm] at lookup
      | arg => simp [LTerm.subterm] at lookup
      | body =>
        apply ih ?_ lookup
        exact ⟨fun x hx => initial.1 x (List.mem_cons_of_mem _ hx),(List.nodup_cons.mp initial.2).2⟩
    | app l f a =>
      cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn =>
        apply ih ?_ lookup
        exact ⟨fun x hx => initial.1 x (List.mem_cons_of_mem _ (List.mem_append_left _ hx)),
          (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).1⟩
      | arg =>
        apply ih ?_ lookup
        exact ⟨fun x hx => initial.1 x (List.mem_cons_of_mem _ (List.mem_append_right _ hx)),
          (List.nodup_append.mp (List.nodup_cons.mp initial.2).2).2.1⟩

/-- The actual one-step head is its old redex and its labelled contractum,
with both lookups recovered from the original StepAt witness. -/
theorem StepAt.head_lookups (step : StepAt head t u) :
    ∃ beta alpha body argument,t.subterm head=some (.app beta (.lam alpha body) argument) ∧
      u.subterm head=some (LTerm.contract beta alpha body argument) := by
  induction step with
  | root beta alpha body argument => exact ⟨beta,alpha,body,argument,rfl,by simp [LTerm.subterm]⟩
  | fn _ ih => exact ih
  | arg _ ih => exact ih
  | body _ ih => exact ih

/-- A supported node for any old subregion of the actual head is necessarily
inside that head, even though reduction may have changed its inner syntax. -/
theorem StepAt.supported_head_node_internal (step : StepAt head t u) (initial : INIT t)
    (atHead : t.subterm head=some headTerm) (atRegion : headTerm.subterm regionSite=some regionTerm)
    (atNode : u.subterm p=some node) (support : node.label.Supported (SourceRegion regionTerm)) :
    ∃ relative,p=head++relative := by
  have headSupport := support.mono (fun n member => LTerm.labels_subset_of_subterm atRegion (Label.atom n) member)
  exact (step.region_cut initial atHead).supported_node_internal initial atHead atNode headSupport
/-- The contractum lookup at a specified real source redex is deterministic. -/
theorem StepAt.contract_lookup {body argument : LTerm} (step : StepAt head t u)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument)) :
    u.subterm head=some (LTerm.contract beta alpha body argument) := by
  obtain ⟨b,a,c,d,old,current⟩ := step.head_lookups
  have same := Option.some.inj (old.symm.trans source)
  simp only [LTerm.app.injEq,LTerm.lam.injEq] at same
  obtain ⟨rfl,⟨rfl,rfl⟩,rfl⟩ := same
  exact current

/-- Contextual argument-side node localization: actual global node paths,
actual argument occurrences and copies are constructed before any local INIT
coordinate is chosen. Outer binders and global atom offsets remain intact. -/
theorem StepAt.argument_subregion_node_locates {body argument regionTerm : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (atRegion : argument.subterm regionSite=some regionTerm)
    (atNode : u.subterm p=some node) (support : node.label.Supported (SourceRegion regionTerm)) :
    ∃ occurrence copy relative,ArgumentOccurrence body.erase occurrence ∧
      u.subterm (head++occurrence)=some copy ∧ LTerm.CopyInterior argument copy ∧
      p=((head++occurrence)++regionSite)++relative := by
  have headInitial := initial.subterm source
  have localRegion : (LTerm.app beta (.lam alpha body) argument).subterm (.arg::regionSite)=some regionTerm := atRegion
  obtain ⟨relative,paths⟩ := step.supported_head_node_internal initial source localRegion atNode support
  have current := step.contract_lookup source
  have localNode : (LTerm.contract beta alpha body argument).subterm relative=some node := by
    rw [paths,LTerm.subterm_append,current] at atNode
    exact atNode
  have coarseSupport := support.mono (fun n member => LTerm.labels_subset_of_subterm atRegion (Label.atom n) member)
  obtain ⟨occurrence,copy,suffix,occurs,atCopy,relativeEq,nonroot,_⟩ :=
    LTerm.contract_supported_node_in_copy (initial_body_outside_argument headInitial) localNode coarseSupport
  have interior := LTerm.contract_argument_copy_interior occurs atCopy
  have copyNode : copy.subterm suffix=some node := by
    rw [relativeEq,LTerm.subterm_append,atCopy] at localNode
    exact localNode
  have argumentInitial : INIT argument := by
    refine ⟨?_,(List.nodup_append.mp (List.nodup_cons.mp headInitial.2).2).2.1⟩
    exact fun l member => headInitial.1 l (List.mem_cons_of_mem _ (List.mem_append_right _ member))
  obtain ⟨rest,regionEq⟩ := interior.region_locates argumentInitial atRegion copyNode support
  refine ⟨occurrence,copy,rest,occurs,?_,interior,?_⟩
  · rw [LTerm.subterm_append,current]
    exact atCopy
  · simp only [paths,relativeEq,regionEq,List.append_assoc]

/-- Contextual body-side localization retains the unique source body path;
all substituted argument labels are excluded using the actual INIT source. -/
theorem StepAt.body_subregion_node_locates {body argument regionTerm : LTerm}
    (step : StepAt head t u) (initial : INIT t)
    (source : t.subterm head=some (.app beta (.lam alpha body) argument))
    (atRegion : body.subterm regionSite=some regionTerm)
    (atNode : u.subterm p=some node) (support : node.label.Supported (SourceRegion regionTerm)) :
    ∃ current suffix,u.subterm (head++regionSite)=some current ∧ p=(head++regionSite)++suffix ∧
      ∀ region,current.label.Supported region → regionTerm.label.Supported region := by
  have headInitial := initial.subterm source
  have localRegion : (LTerm.app beta (.lam alpha body) argument).subterm (.fn::.body::regionSite)=some regionTerm := atRegion
  obtain ⟨relative,paths⟩ := step.supported_head_node_internal initial source localRegion atNode support
  have targetHead := step.contract_lookup source
  have localNode : (LTerm.contract beta alpha body argument).subterm relative=some node := by
    rw [paths,LTerm.subterm_append,targetHead] at atNode
    exact atNode
  obtain ⟨old,oldLookup,sameLabel⟩ := LTerm.contract_supported_body_node_origin
    (initial_argument_outside_body_subregion headInitial atRegion)
    (initial_head_outside_body_subregion headInitial atRegion) localNode support
  have oldSupport : old.label.Supported (SourceRegion regionTerm) := sameLabel ▸ support
  obtain ⟨n,atomic⟩ := headInitial.redex_body.1 old.label (LTerm.label_mem_of_subterm oldLookup)
  have member : old.label∈regionTerm.labels := by
    rw [atomic] at oldSupport ⊢
    exact oldSupport
  obtain ⟨suffix,relativeEq⟩ := LTerm.initial_region_locates body headInitial.redex_body atRegion oldLookup member
  obtain ⟨current,currentLookup,reflects⟩ := LTerm.contract_subterm_root_reflect
    (beta := beta) (alpha := alpha) (argument := argument) atRegion
  exact ⟨current,suffix,by rw [LTerm.subterm_append,targetHead]; exact currentLookup,
    by simp only [paths,relativeEq,List.append_assoc],reflects⟩
end Lamping.Lambda.Labelled
