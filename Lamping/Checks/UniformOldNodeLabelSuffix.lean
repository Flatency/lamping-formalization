import Lamping.Lambda.UniformOldNodeLabelSuffix
import Lamping.Checks.NodeLabelSuffixOrigins
namespace Lamping.Checks.UniformOldNodeLabelSuffixChecks
open Lambda Lambda.Labelled
abbrev I : Term := WrappedSuccessfulChains.I
abbrev caller : Term := .lam (.app I (.var 0))
abbrev bare : Term := .app (.lam (.app (.var 0) (.app (.var 0) I))) caller
abbrev original : LTerm := initLabels bare
abbrev first : LTerm := WrappedSuccessfulChains.contractRoot original
abbrev second : LTerm := WrappedSuccessfulChains.contractRoot first
abbrev source : LTerm := match second with
  | .app stamp fn arg => .app stamp fn (WrappedSuccessfulChains.contractRoot arg)
  | t => t
abbrev middle : LTerm := WrappedSuccessfulChains.contractRoot source
abbrev target : LTerm := WrappedSuccessfulChains.contractRoot middle
abbrev F : List Path := [[],[.arg]]
theorem original_init : INIT original := init_is_INIT _
def globalHistory : History [[],[],[.arg]] original source :=
  .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.cons (.arg (.root _ _ _ _)) (.nil _)))
def labels : History [[],[]] source target :=
  .cons (.root _ _ _ _) (.cons (.root _ _ _ _) (.nil _))
def old : Marked.RelativeOldHistory F [[],[]] (Marked.mark F source.erase) (.lam (.var 0)) :=
  .cons (.redRoot _ _ _) (by decide) (.cons (.redRoot _ _ _) (by decide) (.nil _))
theorem selected (p : Path) (inside : p∈F) : source.degreeAt p=some (.atom 10) := by
  rcases List.mem_cons.mp inside with rfl | inside
  · rfl
  · have same := List.mem_singleton.mp inside;subst p;rfl

abbrev firstArgument : LTerm := match source with | .app _ _ arg => arg | t=>t
abbrev secondArgument : LTerm := match middle with | .app _ _ arg => arg | t=>t
def nodeTrace : BetaNodeHistoryPreimage labels [] [.arg,.arg] := by
  apply BetaNodeHistoryPreimage.one (step:=StepAt.root source.label (.atom 10) (.var (.atom 11) 0) firstArgument)
    (show source.subterm []=some (.app source.label (.lam (.atom 10) (.var (.atom 11) 0)) firstArgument) from rfl)
    (BetaNodePreimage.copied (q:=[]) (relative:=[.arg]) (old:=secondArgument) (by rfl) (by rfl))
  exact BetaNodeHistoryPreimage.one (step:=StepAt.root middle.label (.atom 10) (.var (.atom 11) 0) secondArgument)
    (by rfl) (BetaNodePreimage.copied (q:=[]) (relative:=[]) (old:=secondArgument) (by rfl) (by rfl)) (.nil _ _)

theorem actual_two_step_suffix : ∃node,source.subterm [.arg,.arg]=some node ∧
    (target.label=node.label ∨∃pre marker,marker.MarksDegree (.atom 10) ∧
      target.label.letters=pre++marker::node.label.letters) :=
  old.node_label_suffix (DegreeAligned.initial source F) labels selected nodeTrace rfl

theorem source_safe : source.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  dsimp [source,second,first,original,bare,caller,I,WrappedSuccessfulChains.I,
    WrappedSuccessfulChains.contractRoot,initLabels,initFrom,nodeCount,
    LTerm.contract,LTerm.subst,LTerm.single,LTerm.prepend,LTerm.rename,LTerm.lift,
    LTerm.label,Label.concat,Label.over,Label.under,Label.atom]
  simp only [LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  decide

theorem unsafe_middle : ¬middle.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex (selected [] (by simp [F]))
  exact (StepAt.root _ _ _ _).created_label_not_safe redex (current:=middle) rfl (Or.inl rfl)

theorem target_marked : ¬target.label.OuterBarsSafe (fun x=>x≠Label.atom 10) := by
  obtain ⟨beta,body,argument,redex⟩ := LTerm.degreeAt_redex (by rfl : middle.degreeAt []=some (.atom 10))
  exact (StepAt.root _ _ _ _).created_label_not_safe redex (current:=target) rfl (Or.inl rfl)

theorem actual_original_safe_suffix : ∃node pre marker,
    source.subterm [.arg,.arg]=some node ∧
    node.label.OuterBarsSafe (fun x=>x≠Label.atom 10) ∧marker.MarksDegree (.atom 10) ∧
    target.label.letters=pre++marker::node.label.letters ∧
    target.label.readLetters false=node.label.readLetters false++marker::pre.reverse :=
  old.node_last_marker (DegreeAligned.initial source F) labels selected nodeTrace rfl source_safe target_marked
-- THIS original occurrence is the ARG/ARG node. Its label already has
-- older non-alpha markers: the theorem preserves the ENTIRE compound suffix.
theorem actual_origin_lookup : source.subterm [.arg,.arg]=some secondArgument := rfl

theorem actual_origin_compound : ¬IsAtomic secondArgument.label := by
  rintro ⟨n,equal⟩
  cases equal

theorem actual_complete_original_label : ∃pre marker,marker.MarksDegree (.atom 10) ∧
    target.label.letters=pre++marker::secondArgument.label.letters ∧
    target.label.readLetters false=secondArgument.label.readLetters false++marker::pre.reverse := by
  obtain ⟨node,pre,marker,lookup,safe,marks,equation,reversed⟩ := actual_original_safe_suffix
  have same := Option.some.inj (lookup.symm.trans actual_origin_lookup)
  subst node
  exact ⟨pre,marker,marks,equation,reversed⟩

#print axioms original_init
#print axioms globalHistory
#print axioms labels
#print axioms old
#print axioms nodeTrace
#print axioms actual_two_step_suffix
#print axioms unsafe_middle
#print axioms actual_original_safe_suffix
#print axioms actual_origin_lookup
#print axioms actual_origin_compound
#print axioms actual_complete_original_label
end Lamping.Checks.UniformOldNodeLabelSuffixChecks
