import Lamping.Lambda.NodeLabelSuffixOrigins
import Lamping.Lambda.BetaChainExistenceReflection
import Lamping.Lambda.DegreeFamily
namespace Lamping.Lambda.Labelled

private theorem Label.letters_nonempty (l : Label) : l.letters≠[] := by
  cases l <;> simp [Label.letters]

/-- A literal nonempty old suffix fixes the final atom, independently of
which degrees occurred in the added prefix. -/
private theorem Label.lastAtom_of_letters_suffix {current old : Label} {pre : List Letter}
    (equation : current.letters=pre++old.letters) : current.lastAtom=old.lastAtom := by
  induction pre generalizing current with
  | nil => exact congrArg Label.lastAtom (Label.letters_injective equation)
  | cons letter rest ih =>
    cases current with
    | single a =>
      have tail := (List.cons.inj equation).2
      have empty : rest=[] ∧old.letters=[] := List.append_eq_nil_iff.mp tail.symm
      exact False.elim (old.letters_nonempty empty.2)
    | cons a current => exact ih (current:=current) (List.cons.inj equation).2

/-- Both observations refer to the same actual occurrence preimage. -/
theorem StepAt.beta_node_lastAtom_constructor
    {source target body argument current : LTerm} {site p oldPosition : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (origin : BetaNodePreimage body argument site p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃old,source.subterm oldPosition=some old ∧
      current.label.lastAtom=old.label.lastAtom ∧old.constructorTag=current.constructorTag := by
  obtain ⟨old,atOld,same |⟨pre,marker,_,suffix⟩⟩ := step.beta_node_label_suffix redex origin lookup
  · obtain ⟨other,atOther,tag⟩ := step.preimage_node_constructor redex origin lookup
    have eq := Option.some.inj (atOther.symm.trans atOld)
    subst other
    exact ⟨old,atOld,congrArg Label.lastAtom same,tag⟩
  · obtain ⟨other,atOther,tag⟩ := step.preimage_node_constructor redex origin lookup
    have eq := Option.some.inj (atOther.symm.trans atOld)
    subst other
    exact ⟨old,atOld,Label.lastAtom_of_letters_suffix
      (pre:=pre++[marker]) (by simpa only [List.append_assoc,List.singleton_append] using suffix),tag⟩

/-- Arbitrary full operational history, with no uniform OLD degree or
intermediate safety assumption. Current coordinates remain distinct. -/
theorem BetaNodeHistoryPreimage.lastAtom_constructor
    {ps : List Path} {source target current : LTerm} {labels : History ps source target}
    (trace : BetaNodeHistoryPreimage labels p oldPosition)
    (lookup : target.subterm p=some current) :
    ∃old,source.subterm oldPosition=some old ∧
      current.label.lastAtom=old.label.lastAtom ∧old.constructorTag=current.constructorTag := by
  induction trace with
  | nil => exact ⟨current,lookup,rfl,rfl⟩
  | @one _ _ _ _ _ _ _ _ _ _ _ _ step _ redex origin tail ih =>
    obtain ⟨middle,atMiddle,lastMiddle,tagMiddle⟩ := ih lookup
    obtain ⟨old,atOld,lastOld,tagOld⟩ := step.beta_node_lastAtom_constructor redex origin atMiddle
    exact ⟨old,atOld,lastMiddle.trans lastOld,tagOld.trans tagMiddle⟩

/-- Equal final atoms identify only the ORIGINAL initial occurrence.
No equality of current positions is asserted. -/
theorem History.initial_node_origin_eq_of_lastAtom
    {ps : List Path} {source target left right : LTerm} {p q : Path}
    (labels : History ps source target) (initial : INIT source)
    (atLeft : target.subterm p=some left) (atRight : target.subterm q=some right)
    (same : left.label.lastAtom=right.label.lastAtom) :
    ∃oldPosition old,source.subterm oldPosition=some old ∧
      BetaNodeHistoryPreimage labels p oldPosition ∧BetaNodeHistoryPreimage labels q oldPosition ∧
      old.constructorTag=left.constructorTag ∧old.constructorTag=right.constructorTag := by
  obtain ⟨lp,lold,atLOld,lt⟩ := labels.node_preimage_from_lookup atLeft
  obtain ⟨rp,rold,atROld,rt⟩ := labels.node_preimage_from_lookup atRight
  obtain ⟨l,atL,lastL,tagL⟩ := lt.lastAtom_constructor atLeft
  obtain ⟨r,atR,lastR,tagR⟩ := rt.lastAtom_constructor atRight
  obtain ⟨a,atomicL⟩ := initial.1 l.label (LTerm.label_mem_of_subterm atL)
  obtain ⟨b,atomicR⟩ := initial.1 r.label (LTerm.label_mem_of_subterm atR)
  have atoms : (Label.atom a).lastAtom=(Label.atom b).lastAtom := by
    rw [←atomicL,←atomicR]
    exact lastL.symm.trans (same.trans lastR)
  have equalAtom : a=b := Option.some.inj atoms
  have equalLabel : l.label=r.label := atomicL.trans ((congrArg Label.atom equalAtom).trans atomicR.symm)
  have equalPosition := LTerm.subterm_label_injective source initial.2 atL atR equalLabel
  subst rp
  have equalNode := Option.some.inj (atL.symm.trans atR)
  subst r
  exact ⟨lp,l,atL,lt,rt,tagL,tagR⟩

/-- Same original INIT/history and equal current labels force the same
constructor kind, without identifying the current syntax occurrences. -/
theorem History.node_constructor_eq_of_label
    {ps : List Path} {source target left right : LTerm} {p q : Path}
    (labels : History ps source target) (initial : INIT source)
    (atLeft : target.subterm p=some left) (atRight : target.subterm q=some right)
    (same : left.label=right.label) : left.constructorTag=right.constructorTag := by
  obtain ⟨_,_,_,_,_,leftTag,rightTag⟩ := labels.initial_node_origin_eq_of_lastAtom initial atLeft atRight
    (congrArg Label.lastAtom same)
  exact leftTag.symm.trans rightTag

#print axioms StepAt.beta_node_lastAtom_constructor
#print axioms BetaNodeHistoryPreimage.lastAtom_constructor
#print axioms History.initial_node_origin_eq_of_lastAtom
#print axioms History.node_constructor_eq_of_label
end Lamping.Lambda.Labelled
