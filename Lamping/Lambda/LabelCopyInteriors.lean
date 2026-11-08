import Lamping.Lambda.LabelBetaCopyCover
namespace Lamping.Lambda.Labelled
namespace LTerm

/-- A copied argument has the original syntax and node labels below its
incoming edge; capture avoidance may change indices and prefixes that edge. -/
def CopyInterior (original copy : LTerm) : Prop :=
  ∃ rho word,copy=(original.rename rho).prepend word

theorem CopyInterior.rename (copied : CopyInterior original copy) (tau) :
    CopyInterior original (copy.rename tau) := by
  obtain ⟨rho,word,equal⟩ := copied
  exact ⟨tau ∘ rho,word,by rw [equal,rename_prepend,rename_comp]⟩

theorem CopyInterior.prepend (copied : CopyInterior original copy) (p : Label) :
    CopyInterior original (copy.prepend p) := by
  obtain ⟨rho,word,equal⟩ := copied
  exact ⟨rho,p.concat word,by rw [equal,prepend_assoc]⟩

/-- Every actual put value remains an original argument copy through lifts. -/
theorem lift_copy_interiors
    (copies : ∀ i value,sigma i=.put value → CopyInterior original value) :
    ∀ i value,lift sigma i=.put value → CopyInterior original value := by
  intro i value put
  cases i with
  | zero => cases put
  | succ i =>
    cases he : sigma i with
    | keep j => simp [lift,he] at put
    | put argument =>
      have equal : argument.rename Nat.succ=value := by simpa only [lift,he,SubValue.put.injEq] using put
      exact equal ▸ (copies i argument he).rename Nat.succ

theorem InsertedCopy.copy_interior
    (inserted : InsertedCopy sigma t site copy)
    (copies : ∀ i value,sigma i=.put value → CopyInterior original value) : CopyInterior original copy := by
  induction inserted with
  | here put => exact (copies _ _ put).prepend _
  | fn _ ih => exact ih copies
  | arg _ ih => exact ih copies
  | body _ ih => exact ih (lift_copy_interiors copies)

theorem InsertedCopy.single_interior
    (inserted : InsertedCopy (single (original.prepend word)) t site copy) : CopyInterior original copy := by
  apply inserted.copy_interior
  intro i value put
  cases i with
  | zero =>
    have equal : original.prepend word=value := SubValue.put.inj put
    exact ⟨id,word,by rw [←equal,rename_id]⟩
  | succ i => cases put

/-- Capture-avoiding renaming preserves the labels at every node. -/
theorem rename_label (t : LTerm) (rho) : (t.rename rho).label=t.label := by cases t <;> rfl

theorem subterm_rename (t : LTerm) (rho) (p : Path) :
    ∃ tau,(t.rename rho).subterm p=(t.subterm p).map (LTerm.rename tau) := by
  induction p generalizing t rho with
  | nil => exact ⟨rho,by simp [LTerm.subterm]⟩
  | cons step rest ih =>
    cases t with
    | var l i => cases step <;> exact ⟨rho,rfl⟩
    | lam l b =>
      cases step with
      | fn => exact ⟨rho,rfl⟩
      | arg => exact ⟨rho,rfl⟩
      | body => exact ih b (Lambda.liftRen rho)
    | app l f a =>
      cases step with
      | body => exact ⟨rho,rfl⟩
      | fn => exact ih f rho
      | arg => exact ih a rho

/-- Every nonroot copied node has a real original node at the identical
relative syntax path, carrying exactly the same label. -/
theorem CopyInterior.nonroot_node (copied : CopyInterior original copy)
    (lookup : copy.subterm p=some node) (nonroot : p≠[]) :
    ∃ old,original.subterm p=some old ∧ old.label=node.label := by
  obtain ⟨rho,word,equal⟩ := copied
  rw [equal,prepend_subterm_nonempty _ _ nonroot] at lookup
  obtain ⟨tau,transport⟩ := subterm_rename original rho p
  rw [transport] at lookup
  obtain ⟨old,atOld,same⟩ := Option.map_eq_some_iff.mp lookup
  exact ⟨old,atOld,by rw [←same,rename_label]⟩
/-- A real bound-variable site takes an actual put branch after the exact
number of binder lifts on that syntax path. -/
theorem insertedCopy_of_variable_site (t : LTerm)
    (lookup : subtermAt t.erase p=some (.var (depth+binderDepth p)))
    (put : sigma depth=.put argument) : ∃ copy,InsertedCopy sigma t p copy := by
  induction p generalizing t sigma depth argument with
  | nil =>
    cases t with
    | var l i =>
      have same : i=depth := by simpa [erase,subtermAt,binderDepth] using lookup
      cases same
      exact ⟨_,.here put⟩
    | lam => simp [erase,subtermAt] at lookup
    | app => simp [erase,subtermAt] at lookup
  | cons step rest ih =>
    cases t with
    | var => cases step <;> simp [erase,subtermAt] at lookup
    | app l f a =>
      cases step with
      | body => simp [erase,subtermAt] at lookup
      | fn =>
        obtain ⟨copy,inserted⟩ := ih f lookup put
        exact ⟨copy,.fn inserted⟩
      | arg =>
        obtain ⟨copy,inserted⟩ := ih a lookup put
        exact ⟨copy,.arg inserted⟩
    | lam l b =>
      cases step with
      | fn => simp [erase,subtermAt] at lookup
      | arg => simp [erase,subtermAt] at lookup
      | body =>
        obtain ⟨copy,inserted⟩ := ih b (depth := depth+1) (sigma := lift sigma) (argument := argument.rename Nat.succ) (by
          simpa only [erase,subtermAt,binderDepth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using lookup)
          (congrArg (fun value : SubValue => match value with
            | .keep j => SubValue.keep (j+1)
            | .put a => SubValue.put (a.rename Nat.succ)) put)
        exact ⟨copy,.body inserted⟩

/-- All actual beta argument occurrences yield the expected original-argument
interior, including the body-variable-at-root case with the extra outer prefix. -/
theorem contract_argument_copy_interior {body argument : LTerm}
    (occurs : ArgumentOccurrence body.erase site)
    (lookup : (contract beta alpha body argument).subterm site=some copy) : CopyInterior argument copy := by
  obtain ⟨inserted,putCopy⟩ := insertedCopy_of_variable_site body (depth := 0)
    (sigma := single (argument.prepend alpha.under))
    (by simpa only [Nat.zero_add] using occurs) rfl
  have interior : CopyInterior argument inserted := putCopy.single_interior
  by_cases root : site=[]
  · cases root
    have sourceEq : body.subst (single (argument.prepend alpha.under))=inserted := by
      simpa only [LTerm.subterm,Option.some.injEq] using putCopy.lookup
    have copyEq : inserted.prepend (beta.concat alpha.over)=copy := by
      simpa only [contract,LTerm.subterm,sourceEq,Option.some.injEq] using lookup
    exact copyEq ▸ interior.prepend _
  · have copyEq : inserted=copy := by
      rw [contract,prepend_subterm_nonempty _ _ root] at lookup
      exact Option.some.inj (putCopy.lookup.symm.trans lookup)
    exact copyEq ▸ interior
/-- Prefixing and capture-avoiding renaming cannot make the original root
label regional unless it already was regional. -/
theorem CopyInterior.root_support (copied : CopyInterior original copy)
    (support : copy.label.Supported region) : original.label.Supported region := by
  obtain ⟨rho,word,equal⟩ := copied
  cases equal
  have rootSupport := prepend_root_support (original.rename rho) support
  simpa only [rename_label] using rootSupport

/-- Regional support at any current copied node reflects to a real original
node at the identical relative path, including the incoming root case. -/
theorem CopyInterior.supported_node_origin (copied : CopyInterior original copy)
    (lookup : copy.subterm p=some node) (support : node.label.Supported region) :
    ∃ old,original.subterm p=some old ∧ old.label.Supported region := by
  by_cases root : p=[]
  · cases root
    have equal : copy=node := by simpa only [LTerm.subterm,Option.some.injEq] using lookup
    exact ⟨original,by simp [LTerm.subterm],copied.root_support (equal ▸ support)⟩
  · obtain ⟨old,atOld,same⟩ := copied.nonroot_node lookup root
    exact ⟨old,atOld,same ▸ support⟩

/-- Supported copied nodes locate the actual original subregion, by the
source INIT node identity; current de Bruijn indices play no role in it. -/
theorem CopyInterior.region_locates (copied : CopyInterior original copy) (initial : INIT original)
    (atRegion : original.subterm site=some regionTerm)
    (lookup : copy.subterm p=some node) (support : node.label.Supported (SourceRegion regionTerm)) :
    ∃ suffix,p=site++suffix := by
  obtain ⟨old,atOld,oldSupport⟩ := copied.supported_node_origin lookup support
  obtain ⟨n,atomic⟩ := initial.1 old.label (label_mem_of_subterm atOld)
  have member : old.label∈regionTerm.labels := by
    rw [atomic] at oldSupport ⊢
    exact oldSupport
  exact initial_region_locates original initial atRegion atOld member
end LTerm
end Lamping.Lambda.Labelled
