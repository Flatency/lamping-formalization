import Lamping.Lambda.LabelCopyComponents
namespace Lamping.Lambda.Labelled
namespace LTerm

/-- An actual put branch of labelled substitution, with its retained variable
prefix and the lifted substitution used at that exact variable occurrence. -/
inductive InsertedCopy : (Nat → SubValue) → LTerm → Path → LTerm → Prop where
  | here (put : sigma i=.put argument) :
      InsertedCopy sigma (.var l i) [] (argument.prepend l)
  | fn : InsertedCopy sigma f p copy → InsertedCopy sigma (.app l f a) (.fn::p) copy
  | arg : InsertedCopy sigma a p copy → InsertedCopy sigma (.app l f a) (.arg::p) copy
  | body : InsertedCopy (lift sigma) b p copy → InsertedCopy sigma (.lam l b) (.body::p) copy

theorem InsertedCopy.lookup (inserted : InsertedCopy sigma t site copy) :
    (t.subst sigma).subterm site=some copy := by
  induction inserted with
  | here put => simp [LTerm.subst,put,LTerm.subterm]
  | fn _ ih => exact ih
  | arg _ ih => exact ih
  | body _ ih => exact ih

/-- A nonregional variable's retained prefix makes the copy root nonregional,
regardless of the argument's own label. -/
theorem prepend_root_outside (t : LTerm) (outside : ¬l.Supported region) :
    ¬(t.prepend l).label.Supported region := by
  intro support
  have root : (t.prepend l).label=l.concat t.label := by cases t <;> rfl
  rw [root] at support
  exact outside ((Label.supported_concat _ _ _).mp support).1

/-- Substitution creates regional nodes only strictly inside actual inserted
copies when every original body label is outside the region. -/
theorem subst_supported_node_in_copy (t : LTerm)
    (outside : ∀ l∈t.labels,¬l.Supported region)
    (lookup : (t.subst sigma).subterm p=some node) (support : node.label.Supported region) :
    ∃ site copy suffix,InsertedCopy sigma t site copy ∧ p=site++suffix ∧ suffix≠[] := by
  induction t generalizing sigma p with
  | var l i =>
    have oldOutside : ¬l.Supported region := outside l List.mem_cons_self
    cases put : sigma i with
    | keep j =>
      cases p with
      | nil =>
        have equal : node=.var l j := by simpa [LTerm.subst,put,LTerm.subterm] using lookup.symm
        cases equal
        exact False.elim (oldOutside support)
      | cons step rest => cases step <;> simp [LTerm.subst,put,LTerm.subterm] at lookup
    | put argument =>
      refine ⟨[],argument.prepend l,p,.here put,rfl,?_⟩
      intro empty
      cases empty
      have equal : node=argument.prepend l := by simpa [LTerm.subst,put,LTerm.subterm] using lookup.symm
      cases equal
      exact prepend_root_outside argument oldOutside support
  | lam l b ih =>
    cases p with
    | nil =>
      have equal : node=.lam l (b.subst (lift sigma)) := by simpa [LTerm.subst,LTerm.subterm] using lookup.symm
      cases equal
      exact False.elim (outside l List.mem_cons_self support)
    | cons step rest =>
      cases step with
      | fn => simp [LTerm.subst,LTerm.subterm] at lookup
      | arg => simp [LTerm.subst,LTerm.subterm] at lookup
      | body =>
        obtain ⟨site,copy,suffix,inserted,paths,nonempty⟩ :=
          ih (fun x hx => outside x (List.mem_cons_of_mem _ hx)) lookup
        exact ⟨.body::site,copy,suffix,.body inserted,by simp [paths],nonempty⟩
  | app l f a hf ha =>
    cases p with
    | nil =>
      have equal : node=.app l (f.subst sigma) (a.subst sigma) := by simpa [LTerm.subst,LTerm.subterm] using lookup.symm
      cases equal
      exact False.elim (outside l List.mem_cons_self support)
    | cons step rest =>
      cases step with
      | body => simp [LTerm.subst,LTerm.subterm] at lookup
      | fn =>
        obtain ⟨site,copy,suffix,inserted,paths,nonempty⟩ :=
          hf (fun x hx => outside x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))) lookup
        exact ⟨.fn::site,copy,suffix,.fn inserted,by simp [paths],nonempty⟩
      | arg =>
        obtain ⟨site,copy,suffix,inserted,paths,nonempty⟩ :=
          ha (fun x hx => outside x (List.mem_cons_of_mem _ (List.mem_append_right _ hx))) lookup
        exact ⟨.arg::site,copy,suffix,.arg inserted,by simp [paths],nonempty⟩
/-- The retained old variable prefix excludes every inserted root. -/
theorem InsertedCopy.root_outside (inserted : InsertedCopy sigma t site copy)
    (outside : ∀ l∈t.labels,¬l.Supported region) : ¬copy.label.Supported region := by
  induction inserted with
  | here put => exact prepend_root_outside _ (outside _ List.mem_cons_self)
  | fn _ ih => exact ih (fun l hl => outside l (List.mem_cons_of_mem _ (List.mem_append_left _ hl)))
  | arg _ ih => exact ih (fun l hl => outside l (List.mem_cons_of_mem _ (List.mem_append_right _ hl)))
  | body _ ih => exact ih (fun l hl => outside l (List.mem_cons_of_mem _ hl))

theorem lift_put_index (index : ∀ i argument,sigma i=.put argument → i=depth) :
    ∀ i argument,lift sigma i=.put argument → i=depth+1 := by
  intro i argument put
  cases i with
  | zero => cases put
  | succ i =>
    cases value : sigma i with
    | keep j => simp [lift,value] at put
    | put a => exact congrArg Nat.succ (index i a value)

/-- Single-variable beta substitution uses the contracted binder's actual
variable occurrences, with the de Bruijn depth checked under every lambda. -/
theorem InsertedCopy.variable_site (inserted : InsertedCopy sigma t site copy)
    (index : ∀ i argument,sigma i=.put argument → i=depth) :
    subtermAt t.erase site=some (.var (depth+binderDepth site)) := by
  induction inserted generalizing depth with
  | here put => simp [LTerm.erase,subtermAt,binderDepth,index _ _ put]
  | fn _ ih => exact ih index
  | arg _ ih => exact ih index
  | body _ ih =>
    have inside := ih (lift_put_index index)
    simpa only [LTerm.erase,subtermAt,binderDepth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using inside

theorem InsertedCopy.argument_occurrence {body : LTerm} (inserted : InsertedCopy (single argument) body site copy) :
    ArgumentOccurrence body.erase site := by
  have index : ∀ i a,single argument i=.put a → i=0 := by
    intro i a put
    cases i with
    | zero => rfl
    | succ i => cases put
  simpa only [ArgumentOccurrence,Nat.zero_add] using inserted.variable_site index

/-- Different inserted beta arguments are actual disjoint occurrences. -/
theorem InsertedCopy.disjoint {body : LTerm} (left : InsertedCopy (single argument) body p a)
    (right : InsertedCopy (single argument) body q b) (different : p≠q) :
    DisjointPositions p q := left.argument_occurrence.disjoint_of_ne right.argument_occurrence different
/-- Prepending affects only the incoming root edge. -/
theorem prepend_subterm_nonempty (t : LTerm) (l : Label) (nonempty : p≠[]) :
    (t.prepend l).subterm p=t.subterm p := by
  cases p with
  | nil => exact False.elim (nonempty rfl)
  | cons step rest => cases t <;> cases step <;> rfl

theorem prepend_root_support (t : LTerm) (support : (t.prepend l).label.Supported region) :
    t.label.Supported region := by
  have root : (t.prepend l).label=l.concat t.label := by cases t <;> rfl
  exact ((Label.supported_concat _ _ _).mp (root ▸ support)).2

/-- A supported node after genuine beta contraction lies strictly below a
real argument-copy root. Both root lookup and original ArgumentOccurrence
are constructed; no copy index or localization conclusion is assumed. -/
theorem contract_supported_node_in_copy {body argument : LTerm}
    (outside : ∀ l∈body.labels,¬l.Supported region)
    (lookup : (contract beta alpha body argument).subterm p=some node)
    (support : node.label.Supported region) :
    ∃ site copy suffix,ArgumentOccurrence body.erase site ∧
      (contract beta alpha body argument).subterm site=some copy ∧
      p=site++suffix ∧ suffix≠[] ∧ ¬copy.label.Supported region := by
  let substituted := body.subst (single (argument.prepend alpha.under))
  have pNonempty : p≠[] := by
    intro empty
    cases empty
    have equal : node=substituted.prepend (beta.concat alpha.over) := by
      simpa only [contract,LTerm.subterm,Option.some.injEq] using lookup.symm
    have oldSupport : substituted.label.Supported region := prepend_root_support substituted (equal ▸ support)
    have rootLookup : substituted.subterm []=some substituted := by simp [LTerm.subterm]
    obtain ⟨site,copy,suffix,inserted,paths,nonempty⟩ :=
      subst_supported_node_in_copy body outside rootLookup oldSupport
    have lengths := congrArg List.length paths
    simp only [List.length_nil,List.length_append] at lengths
    exact nonempty (List.eq_nil_of_length_eq_zero (by omega))
  have oldLookup : substituted.subterm p=some node := by
    rw [contract,prepend_subterm_nonempty _ _ pNonempty] at lookup
    exact lookup
  obtain ⟨site,copy,suffix,inserted,paths,nonempty⟩ :=
    subst_supported_node_in_copy body outside oldLookup support
  by_cases root : site=[]
  · cases root
    have copyEq : substituted=copy := by
      simpa only [LTerm.subterm,Option.some.injEq] using inserted.lookup
    refine ⟨[],copy.prepend (beta.concat alpha.over),suffix,inserted.argument_occurrence,?_,paths,nonempty,?_⟩
    · simpa only [contract,LTerm.subterm] using congrArg (fun x => some (x.prepend (beta.concat alpha.over))) copyEq
    · intro copySupport
      exact inserted.root_outside outside (prepend_root_support copy copySupport)
  · exact ⟨site,copy,suffix,inserted.argument_occurrence,by
      rw [contract,prepend_subterm_nonempty _ _ root]
      exact inserted.lookup,paths,nonempty,inserted.root_outside outside⟩
end LTerm
end Lamping.Lambda.Labelled
