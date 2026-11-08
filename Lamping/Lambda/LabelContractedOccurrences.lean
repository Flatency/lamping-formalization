import Lamping.Lambda.LabelCanonicalFirstRedex
namespace Lamping.Lambda.Labelled
namespace LTerm

/-- Only strict descendants of a put value are required to use the region.
The incoming root is stamped by the old variable when substitution occurs. -/
private def StrictPutSupport (region : Nat → Prop) (value : LTerm) : Prop :=
  ∀ {p node},value.subterm p=some node → p≠[] → node.label.Supported region

private theorem StrictPutSupport.rename (guard : StrictPutSupport region value) (rho) :
    StrictPutSupport region (value.rename rho) := by
  intro p node lookup nonempty
  obtain ⟨tau,transport⟩ := subterm_rename value rho p
  rw [transport] at lookup
  obtain ⟨old,oldLookup,equal⟩ := Option.map_eq_some_iff.mp lookup
  rw [←equal,rename_label]
  exact guard oldLookup nonempty

private theorem lift_strict_put_support
    (guard : ∀ i value,sigma i=.put value → StrictPutSupport region value) :
    ∀ i value,lift sigma i=.put value → StrictPutSupport region value := by
  intro i value put
  cases i with
  | zero => cases put
  | succ i =>
    cases actual : sigma i with
    | keep j => simp [lift,actual] at put
    | put argument =>
      have equal : argument.rename Nat.succ=value := by simpa only [lift,actual,SubValue.put.injEq] using put
      exact equal ▸ (@StrictPutSupport.rename region argument (guard i argument actual) Nat.succ)

/-- A node not wholly supported by copied interiors retains its old syntax
path and its old first atom, including the stamp on an inserted root. -/
private theorem subst_first_origin (t : LTerm)
    (guard : ∀ i value,sigma i=.put value → StrictPutSupport region value)
    (lookup : (t.subst sigma).subterm p=some node) (outside : ¬node.label.Supported region) :
    ∃ old,t.subterm p=some old ∧ node.label.firstAtom=old.label.firstAtom := by
  induction t generalizing sigma p with
  | var label index =>
    cases put : sigma index with
    | keep j =>
      cases p with
      | nil =>
        have equal : node=.var label j := by simpa [subst,put,subterm] using lookup.symm
        exact ⟨.var label index,rfl,by rw [equal]; rfl⟩
      | cons step rest => cases step <;> simp [subst,put,subterm] at lookup
    | put value =>
      cases p with
      | nil =>
        have equal : node=value.prepend label := by simpa [subst,put,subterm] using lookup.symm
        refine ⟨.var label index,rfl,?_⟩
        rw [equal]
        have root : (value.prepend label).label=label.concat value.label := by cases value <;> rfl
        exact root ▸ Label.firstAtom_concat label value.label
      | cons step rest =>
        have inner : value.subterm (step::rest)=some node := by
          simpa only [subst,put,prepend_subterm_nonempty _ _ (List.cons_ne_nil _ _)] using lookup
        exact False.elim (outside (guard index value put inner (List.cons_ne_nil _ _)))
  | lam label body ih =>
    cases p with
    | nil =>
      have equal : node=.lam label (body.subst (lift sigma)) := by simpa [subst,subterm] using lookup.symm
      exact ⟨.lam label body,rfl,by rw [equal]; rfl⟩
    | cons step rest =>
      cases step with
      | fn => simp [subst,subterm] at lookup
      | arg => simp [subst,subterm] at lookup
      | body =>
        obtain ⟨old,oldLookup,first⟩ := ih (lift_strict_put_support guard) lookup
        exact ⟨old,oldLookup,first⟩
  | app label fn arg hf ha =>
    cases p with
    | nil =>
      have equal : node=.app label (fn.subst sigma) (arg.subst sigma) := by simpa [subst,subterm] using lookup.symm
      exact ⟨.app label fn arg,rfl,by rw [equal]; rfl⟩
    | cons step rest =>
      cases step with
      | body => simp [subst,subterm] at lookup
      | fn => exact hf guard lookup
      | arg => exact ha guard lookup

private theorem single_strict_put_support (argument : LTerm) (initial : INIT argument) :
    ∀ i value,single (argument.prepend word) i=.put value → StrictPutSupport (SourceRegion argument) value := by
  intro i value put
  cases i with
  | succ i => cases put
  | zero =>
    have equal : value=argument.prepend word := (SubValue.put.inj put).symm
    cases equal
    intro p node lookup nonempty
    rw [prepend_subterm_nonempty _ _ nonempty] at lookup
    have member := label_mem_of_subterm lookup
    obtain ⟨n,atomic⟩ := initial.1 node.label member
    rw [atomic] at member ⊢
    exact member

/-- A strict non-argument-supported contractum node retains the old body
occurrence's first atom at the identical path. -/
theorem contract_nonroot_first_origin {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (lookup : (contract beta alpha body argument).subterm p=some node)
    (nonroot : p≠[]) (outside : ¬node.label.Supported (SourceRegion argument)) :
    ∃ old,body.subterm p=some old ∧ node.label.firstAtom=old.label.firstAtom := by
  have argInitial : INIT argument := initial.subterm (p := [.arg]) (by simp [subterm])
  rw [contract,prepend_subterm_nonempty _ _ nonroot] at lookup
  exact subst_first_origin body (single_strict_put_support argument argInitial) lookup outside

private theorem contract_root_first (beta alpha : Label) (body argument : LTerm) :
    (contract beta alpha body argument).label.firstAtom=beta.firstAtom := by
  unfold contract
  generalize body.subst (single (argument.prepend alpha.under))=value
  cases value <;> simp only [prepend,label,Label.firstAtom_concat]

private theorem nonroot_first_ne_root {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (lookup : (contract beta alpha body argument).subterm p=some node)
    (nonroot : p≠[]) (outside : ¬node.label.Supported (SourceRegion argument)) :
    node.label.firstAtom≠beta.firstAtom := by
  obtain ⟨old,oldLookup,first⟩ := contract_nonroot_first_origin initial lookup nonroot outside
  have member := label_mem_of_subterm oldLookup
  have inSource : old.label∈(LTerm.app beta (.lam alpha body) argument).labels :=
    List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _ member))
  obtain ⟨b,betaAtom⟩ := initial.1 beta List.mem_cons_self
  obtain ⟨n,oldAtom⟩ := initial.1 old.label inSource
  intro equal
  have names : n=b := by
    have atoms := first.symm.trans equal
    rw [oldAtom,betaAtom] at atoms
    exact Option.some.inj atoms
  have labels : old.label=beta := oldAtom.trans ((congrArg Label.atom names).trans betaAtom.symm)
  have absent := (List.nodup_cons.mp initial.2).1
  exact absent (labels ▸ List.mem_append_left _ (List.mem_cons_of_mem _ member))

/-- The single-beta edge-image collision kernel: outside pure argument
interiors, equal actual target labels determine the actual syntax occurrence.
No local INIT substitution, node map or route is assumed injective. -/
theorem contract_outside_label_injective {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (left : (contract beta alpha body argument).subterm p=some node)
    (right : (contract beta alpha body argument).subterm q=some other)
    (same : node.label=other.label) (outside : ¬node.label.Supported (SourceRegion argument)) : p=q := by
  have otherOutside : ¬other.label.Supported (SourceRegion argument) := same ▸ outside
  cases p with
  | nil =>
    cases q with
    | nil => rfl
    | cons step rest =>
      have rootEq : node=contract beta alpha body argument := by simpa only [subterm,Option.some.injEq] using left.symm
      have first : other.label.firstAtom=beta.firstAtom := by rw [←same,rootEq,contract_root_first]
      exact False.elim (nonroot_first_ne_root initial right (List.cons_ne_nil _ _) otherOutside first)
  | cons step rest =>
    cases q with
    | nil =>
      have rootEq : other=contract beta alpha body argument := by simpa only [subterm,Option.some.injEq] using right.symm
      have first : node.label.firstAtom=beta.firstAtom := by rw [same,rootEq,contract_root_first]
      exact False.elim (nonroot_first_ne_root initial left (List.cons_ne_nil _ _) outside first)
    | cons next tail =>
      obtain ⟨old,leftOld,leftFirst⟩ := contract_nonroot_first_origin initial left (List.cons_ne_nil _ _) outside
      obtain ⟨oldOther,rightOld,rightFirst⟩ := contract_nonroot_first_origin initial right (List.cons_ne_nil _ _) otherOutside
      have bodyInitial : INIT body := initial.subterm (p := [.fn,.body]) (by simp [subterm])
      obtain ⟨n,oldAtom⟩ := bodyInitial.1 old.label (label_mem_of_subterm leftOld)
      obtain ⟨m,otherAtom⟩ := bodyInitial.1 oldOther.label (label_mem_of_subterm rightOld)
      have names : n=m := by
        have first := leftFirst.symm.trans ((congrArg Label.firstAtom same).trans rightFirst)
        rw [oldAtom,otherAtom] at first
        exact Option.some.inj first
      exact subterm_label_injective body bodyInitial.2 leftOld rightOld
        (oldAtom.trans ((congrArg Label.atom names).trans otherAtom.symm))

/-- Different target occurrences with the same label are wholly supported
by the original argument. This is a node/edge-image statement, not yet a
whole-path reflection theorem. -/
theorem contract_label_collision_argument {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (left : (contract beta alpha body argument).subterm p=some node)
    (right : (contract beta alpha body argument).subterm q=some other)
    (same : node.label=other.label) (different : p≠q) : node.label.Supported (SourceRegion argument) := by
  classical
  by_cases support : node.label.Supported (SourceRegion argument)
  · exact support
  · exact False.elim (different (contract_outside_label_injective initial left right same support))
/-- Every nontrivial label collision has two genuinely different argument
occurrences, with strict descendant coordinates in both actual copies. -/
theorem contract_collision_distinct_copies {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (left : (contract beta alpha body argument).subterm p=some node)
    (right : (contract beta alpha body argument).subterm q=some other)
    (same : node.label=other.label) (different : p≠q) :
    ∃ leftSite rightSite leftCopy rightCopy leftRelative rightRelative,
      ArgumentOccurrence body.erase leftSite ∧ ArgumentOccurrence body.erase rightSite ∧ leftSite≠rightSite ∧
      (contract beta alpha body argument).subterm leftSite=some leftCopy ∧
      (contract beta alpha body argument).subterm rightSite=some rightCopy ∧
      p=leftSite++leftRelative ∧ q=rightSite++rightRelative ∧ leftRelative≠[] ∧ rightRelative≠[] := by
  have support := contract_label_collision_argument initial left right same different
  have otherSupport : other.label.Supported (SourceRegion argument) := same ▸ support
  have outside := initial_body_outside_argument initial
  obtain ⟨leftSite,leftCopy,leftRelative,leftOccurs,leftLookup,leftPath,leftStrict,_⟩ :=
    contract_supported_node_in_copy outside left support
  obtain ⟨rightSite,rightCopy,rightRelative,rightOccurs,rightLookup,rightPath,rightStrict,_⟩ :=
    contract_supported_node_in_copy outside right otherSupport
  refine ⟨leftSite,rightSite,leftCopy,rightCopy,leftRelative,rightRelative,leftOccurs,rightOccurs,?_,
    leftLookup,rightLookup,leftPath,rightPath,leftStrict,rightStrict⟩
  intro sameSite
  subst rightSite
  have sameCopy : leftCopy=rightCopy := Option.some.inj (leftLookup.symm.trans rightLookup)
  subst rightCopy
  have leftAt : leftCopy.subterm leftRelative=some node := by
    rw [leftPath,subterm_append,leftLookup] at left
    exact left
  have rightAt : leftCopy.subterm rightRelative=some other := by
    rw [rightPath,subterm_append,leftLookup] at right
    exact right
  have interior := contract_argument_copy_interior leftOccurs leftLookup
  obtain ⟨old,leftOld,leftLabel⟩ := interior.nonroot_node leftAt leftStrict
  obtain ⟨oldOther,rightOld,rightLabel⟩ := interior.nonroot_node rightAt rightStrict
  have argInitial : INIT argument := initial.subterm (p := [.arg]) (by simp [subterm])
  have relativeEq := subterm_label_injective argument argInitial.2 leftOld rightOld
    (leftLabel.trans (same.trans rightLabel.symm))
  exact different (leftPath.trans ((congrArg (leftSite++·) relativeEq).trans rightPath.symm))
end LTerm
/-- Single-beta edge substitution is injective on actual local INIT edges
whose common image is not wholly an original argument-interior word. -/
theorem root_beta_outside_edge_injective {body argument : LTerm}
    (initial : INIT (.app beta (.lam alpha body) argument))
    (left : e∈sourceEdges [] .external (initLabels (LTerm.contract beta alpha body argument).erase))
    (right : f∈sourceEdges [] .external (initLabels (LTerm.contract beta alpha body argument).erase))
    (same : e.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)=
      f.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0))
    (outside : ¬(e.atom.relabel (initialRelabelling (LTerm.contract beta alpha body argument) 0)).Supported
      (SourceRegion argument)) : e=f := by
  let target := LTerm.contract beta alpha body argument
  let basis := initLabels target.erase
  have leftMember : e.atom∈basis.labels := by
    rw [←sourceEdges_atoms basis [] .external]
    exact List.mem_map.mpr ⟨e,left,rfl⟩
  have rightMember : f.atom∈basis.labels := by
    rw [←sourceEdges_atoms basis [] .external]
    exact List.mem_map.mpr ⟨f,right,rfl⟩
  obtain ⟨p,node,leftAt,leftLabel⟩ := LTerm.label_mem_located basis leftMember
  obtain ⟨q,other,rightAt,rightLabel⟩ := LTerm.label_mem_located basis rightMember
  have currentLeft := LTerm.basis_node_transport target leftAt
  have currentRight := LTerm.basis_node_transport target rightAt
  have labels : (node.relabel (initialRelabelling target 0)).label=
      (other.relabel (initialRelabelling target 0)).label := by
    simpa only [LTerm.label_relabel,leftLabel,rightLabel] using same
  have notArgument : ¬(node.relabel (initialRelabelling target 0)).label.Supported (SourceRegion argument) := by
    simpa only [LTerm.label_relabel,leftLabel] using outside
  have samePath := LTerm.contract_outside_label_injective initial currentLeft currentRight labels notArgument
  cases samePath
  have nodes : node=other := Option.some.inj (leftAt.symm.trans rightAt)
  have atoms : e.atom=f.atom := leftLabel.symm.trans ((congrArg LTerm.label nodes).trans rightLabel)
  exact sourceEdges_unique (init_is_INIT target.erase) left right atoms
end Lamping.Lambda.Labelled







