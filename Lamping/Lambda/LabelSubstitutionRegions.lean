import Lamping.Lambda.LabelArgumentSubregions
namespace Lamping.Lambda.Labelled
namespace LTerm

/-- No node label is wholly supported by the specified source region. -/
def OutsideRegion (region : Nat → Prop) (t : LTerm) : Prop :=
  ∀ l∈t.labels,¬l.Supported region

theorem OutsideRegion.rename (outside : OutsideRegion region t) (rho) :
    OutsideRegion region (t.rename rho) := by
  induction t generalizing rho with
  | var l i => exact outside
  | lam l b ih =>
    intro x member
    rcases List.mem_cons.mp member with same | inside
    · cases same; exact outside l List.mem_cons_self
    · exact ih (fun x hx => outside x (List.mem_cons_of_mem _ hx)) _ x inside
  | app l f a hf ha =>
    intro x member
    rcases List.mem_cons.mp member with same | inside
    · cases same; exact outside l List.mem_cons_self
    · rcases List.mem_append.mp inside with left | right
      · exact hf (fun x hx => outside x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))) _ x left
      · exact ha (fun x hx => outside x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))) _ x right

theorem OutsideRegion.prepend (outside : OutsideRegion region t) (word : Label) :
    OutsideRegion region (t.prepend word) := by
  cases t with
  | var l i =>
    intro x member
    have same : x=word.concat l := List.mem_singleton.mp member
    cases same
    intro support
    exact outside l List.mem_cons_self ((Label.supported_concat _ _ _).mp support).2
  | lam l b =>
    intro x member
    rcases List.mem_cons.mp member with same | inside
    · cases same
      intro support
      exact outside l List.mem_cons_self ((Label.supported_concat _ _ _).mp support).2
    · exact outside x (List.mem_cons_of_mem _ inside)
  | app l f a =>
    intro x member
    rcases List.mem_cons.mp member with same | inside
    · cases same
      intro support
      exact outside l List.mem_cons_self ((Label.supported_concat _ _ _).mp support).2
    · exact outside x (List.mem_cons_of_mem _ inside)

/-- Every substituted root retains the old root label as an outer prefix or
as the unchanged root of an app/lambda. -/
theorem subst_root_support (t : LTerm) (support : (t.subst sigma).label.Supported region) :
    t.label.Supported region := by
  cases t with
  | var l i =>
    cases he : sigma i with
    | keep j => simpa only [LTerm.subst,he,LTerm.label] using support
    | put u =>
      have root : (u.prepend l).label=l.concat u.label := by cases u <;> rfl
      have supported : (l.concat u.label).Supported region := by
        simpa only [LTerm.subst,he,root] using support
      exact ((Label.supported_concat _ _ _).mp supported).1
  | lam => exact support
  | app => exact support

theorem lift_outside_values
    (values : ∀ i value,sigma i=.put value → OutsideRegion region value) :
    ∀ i value,lift sigma i=.put value → OutsideRegion region value := by
  intro i value put
  cases i with
  | zero => cases put
  | succ i =>
    cases he : sigma i with
    | keep j => simp [lift,he] at put
    | put u =>
      have equal : u.rename Nat.succ=value := by simpa only [lift,he,SubValue.put.injEq] using put
      exact equal ▸ (values i u he).rename Nat.succ

/-- Put values outside a region cannot supply a supported node. Such a node
must be a retained original body node at the identical actual syntax path. -/
theorem subst_supported_node_origin (t : LTerm)
    (values : ∀ i value,sigma i=.put value → OutsideRegion region value)
    (lookup : (t.subst sigma).subterm p=some node) (support : node.label.Supported region) :
    ∃ old,t.subterm p=some old ∧ old.label=node.label := by
  induction t generalizing sigma p with
  | var l i =>
    cases he : sigma i with
    | keep j =>
      cases p with
      | nil =>
        have same : node=.var l j := by simpa only [LTerm.subst,he,LTerm.subterm,Option.some.injEq] using lookup.symm
        cases same
        exact ⟨.var l i,rfl,rfl⟩
      | cons step rest => cases step <;> simp [LTerm.subst,he,LTerm.subterm] at lookup
    | put u =>
      have outside := (values i u he).prepend l
      have member : node.label∈(u.prepend l).labels := by
        apply label_mem_of_subterm
        simpa only [LTerm.subst,he] using lookup
      exact False.elim (outside node.label member support)
  | lam l b ih =>
    cases p with
    | nil =>
      have same : node=.lam l (b.subst (lift sigma)) := by simpa only [LTerm.subst,LTerm.subterm,Option.some.injEq] using lookup.symm
      cases same
      exact ⟨.lam l b,rfl,rfl⟩
    | cons step rest =>
      cases step with
      | fn => simp [LTerm.subst,LTerm.subterm] at lookup
      | arg => simp [LTerm.subst,LTerm.subterm] at lookup
      | body =>
        obtain ⟨old,atOld,equal⟩ := ih (lift_outside_values values) lookup
        exact ⟨old,atOld,equal⟩
  | app l f a hf ha =>
    cases p with
    | nil =>
      have same : node=.app l (f.subst sigma) (a.subst sigma) := by simpa only [LTerm.subst,LTerm.subterm,Option.some.injEq] using lookup.symm
      cases same
      exact ⟨.app l f a,rfl,rfl⟩
    | cons step rest =>
      cases step with
      | body => simp [LTerm.subst,LTerm.subterm] at lookup
      | fn =>
        obtain ⟨old,atOld,equal⟩ := hf values lookup
        exact ⟨old,atOld,equal⟩
      | arg =>
        obtain ⟨old,atOld,equal⟩ := ha values lookup
        exact ⟨old,atOld,equal⟩
/-- Every original source subterm still has a root at the same path after
substitution, and support of that root reflects to its original label. -/
theorem subst_subterm_root_reflect (t : LTerm) (oldLookup : t.subterm p=some old) (sigma) :
    ∃ current,(t.subst sigma).subterm p=some current ∧
      ∀ region,current.label.Supported region → old.label.Supported region := by
  induction p generalizing t sigma with
  | nil =>
    have same : t=old := by simpa only [LTerm.subterm,Option.some.injEq] using oldLookup
    cases same
    exact ⟨old.subst sigma,by simp [LTerm.subterm],fun _ support => subst_root_support old support⟩
  | cons step rest ih =>
    cases t with
    | var => cases step <;> simp [LTerm.subterm] at oldLookup
    | lam l b =>
      cases step with
      | fn => simp [LTerm.subterm] at oldLookup
      | arg => simp [LTerm.subterm] at oldLookup
      | body => exact ih b oldLookup (lift sigma)
    | app l f a =>
      cases step with
      | body => simp [LTerm.subterm] at oldLookup
      | fn => exact ih f oldLookup sigma
      | arg => exact ih a oldLookup sigma

/-- The extra beta prefix affects only the root edge; old root support still
reflects even when the selected original body subterm is the whole body. -/
theorem contract_subterm_root_reflect {body argument : LTerm}
    (oldLookup : body.subterm p=some old) :
    ∃ current,(contract beta alpha body argument).subterm p=some current ∧
      ∀ region,current.label.Supported region → old.label.Supported region := by
  obtain ⟨current,lookup,reflects⟩ := subst_subterm_root_reflect body oldLookup
    (single (argument.prepend alpha.under))
  by_cases root : p=[]
  · cases root
    have currentEq : body.subst (single (argument.prepend alpha.under))=current := by
      simpa only [LTerm.subterm,Option.some.injEq] using lookup
    refine ⟨current.prepend (beta.concat alpha.over),?_,?_⟩
    · simp only [contract,LTerm.subterm,currentEq]
    · exact fun region support => reflects region (prepend_root_support current support)
  · exact ⟨current,by rw [contract,prepend_subterm_nonempty _ _ root]; exact lookup,reflects⟩

/-- When the argument and fired degree are outside a body region, every
supported target node is a retained original body node at the same path.
This is the actual body-side companion of the argument-copy localization. -/
theorem contract_supported_body_node_origin {body argument : LTerm}
    (argOutside : OutsideRegion region argument) (headOutside : ¬alpha.Supported region)
    (lookup : (contract beta alpha body argument).subterm p=some node)
    (support : node.label.Supported region) :
    ∃ old,body.subterm p=some old ∧ old.label=node.label := by
  have outerOutside : ¬(beta.concat alpha.over).Supported region := by
    intro supported
    exact headOutside ((Label.supported_concat _ _ _).mp supported).2
  have nonroot : p≠[] := by
    intro empty
    cases empty
    have same : node=(body.subst (single (argument.prepend alpha.under))).prepend (beta.concat alpha.over) := by
      simpa only [contract,LTerm.subterm,Option.some.injEq] using lookup.symm
    exact prepend_root_outside _ outerOutside (same ▸ support)
  have innerLookup : (body.subst (single (argument.prepend alpha.under))).subterm p=some node := by
    rw [contract,prepend_subterm_nonempty _ _ nonroot] at lookup
    exact lookup
  have outsideValues : ∀ i value,single (argument.prepend alpha.under) i=.put value → OutsideRegion region value := by
    intro i value put
    cases i with
    | zero =>
      have same : argument.prepend alpha.under=value := SubValue.put.inj put
      exact same ▸ argOutside.prepend alpha.under
    | succ i => cases put
  exact subst_supported_node_origin body outsideValues innerLookup support
end LTerm
end Lamping.Lambda.Labelled
