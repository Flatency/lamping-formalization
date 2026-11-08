import Lamping.Lambda.LabelContextualCopyCover
namespace Lamping.Lambda.Labelled

/-- A real beta root retains the old app label as a prefix; all contextual
steps leave the root label unchanged. Regional root support reflects back. -/
theorem StepAt.root_support (step : StepAt p t u) (support : u.label.Supported region) :
    t.label.Supported region := by
  cases step with
  | root beta alpha body argument =>
    -- Root support also includes the prepended old application label.
    have root : (LTerm.contract beta alpha body argument).label=
        (beta.concat alpha.over).concat (body.subst (LTerm.single (argument.prepend alpha.under))).label := by
      unfold LTerm.contract
      cases body.subst (LTerm.single (argument.prepend alpha.under)) <;> rfl
    have whole : ((beta.concat alpha.over).concat
        (body.subst (LTerm.single (argument.prepend alpha.under))).label).Supported region := root ▸ support
    exact ((Label.supported_concat _ _ _).mp ((Label.supported_concat _ _ _).mp whole).1).1
  | fn => exact support
  | arg => exact support
  | body => exact support

theorem History.root_support (history : History ps t u) (support : u.label.Supported region) :
    t.label.Supported region := by
  induction history with
  | nil => exact support
  | cons step tail ih => exact step.root_support (ih support)

/-- An actual internal history yields an actual local history, so the
current region root retains the old root's support obligations. -/
theorem History.internal_root_support (history : History ps t u)
    (atSite : t.subterm site=some subtree) (inside : ∀ p∈ps,∃ suffix,p=site++suffix)
    (atCurrent : u.subterm site=some current) (support : current.label.Supported region) :
    subtree.label.Supported region := by
  obtain ⟨result,currentLookup,localHistory⟩ := history.subterm_internal atSite inside
  have same : result=current := Option.some.inj (currentLookup.symm.trans atCurrent)
  exact localHistory.root_support (same ▸ support)
/-- Strict regional support survives the actual local INIT coordinate change
after an internal prefix. The new root edge cannot be used, because its
image still contains the original root's support obligation. -/
theorem History.internal_strict_region_transport
    (prefixHistory : History ps t u) (initial : INIT t)
    (atSite : t.subterm site=some subtree) (inside : ∀ p∈ps,∃ suffix,p=site++suffix)
    (globalTail : History qs u v) (basisTail : History qs (initLabels u.erase) z)
    (globalDegree : v.degreeAt p=some globalLabel) (basisDegree : z.degreeAt p=some basisLabel)
    (support : globalLabel.Supported (SourceRegion subtree))
    (rootAvoid : globalLabel.Supported (fun n => Label.atom n≠subtree.label)) :
    ∃ basisSubtree,(initLabels u.erase).subterm site=some basisSubtree ∧
      basisLabel.Supported (SourceRegion basisSubtree) ∧
      ∀ e∈basisLabel.edgeWord,Label.atom e.atom≠basisSubtree.label := by
  obtain ⟨basisSubtree,atBasis,transported,reflection⟩ :=
    prefixHistory.local_degree_region_reflection initial atSite inside globalTail basisTail basisDegree
  have labelEq : basisLabel.relabel (initialRelabelling u 0)=globalLabel :=
    Option.some.inj (transported.symm.trans globalDegree)
  have localSupport := reflection.mp (labelEq.symm ▸ support)
  have localAvoid := (Label.supported_relabel _ _ basisLabel).mp (labelEq.symm ▸ rootAvoid)
  have wordAvoid := (Label.supported_iff_within _ basisLabel).mp localAvoid
  refine ⟨basisSubtree,atBasis,localSupport,?_⟩
  intro e member sameRoot
  have currentLookup := LTerm.basis_node_transport u atBasis
  have currentRoot : (basisSubtree.relabel (initialRelabelling u 0)).label.Supported
      (fun n => Label.atom n≠subtree.label) := by
    rw [LTerm.label_relabel,←sameRoot,Label.relabel_atom]
    exact wordAvoid e member
  have oldAvoid := prefixHistory.internal_root_support atSite inside currentLookup currentRoot
  obtain ⟨n,atomic⟩ := initial.1 subtree.label (LTerm.label_mem_of_subterm atSite)
  rw [atomic] at oldAvoid
  exact oldAvoid rfl
end Lamping.Lambda.Labelled
