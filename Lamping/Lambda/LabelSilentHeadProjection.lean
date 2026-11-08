import Lamping.Lambda.LabelSilentHeadLocality
namespace Lamping.Lambda.Labelled

/-- Project a real coloured internal history to its actual subtree. Every
local degree is the very same label, at the dropped actual site. -/
theorem RegionalHistory.subterm_internal (regional : RegionalHistory region ps t u)
    (atSite : t.subterm site=some subtree) (inside : ∀ p∈ps,∃ suffix,p=site++suffix) :
    ∃ result,u.subterm site=some result ∧
      RegionalHistory region (ps.map (List.drop site.length)) subtree result := by
  induction regional generalizing subtree with
  | nil t => exact ⟨subtree,atSite,.nil _⟩
  | @cons p t middle l ps u step degree support rest ih =>
    obtain ⟨suffix,equal⟩ := inside p List.mem_cons_self
    cases equal
    obtain ⟨part,atMiddle,localStep⟩ := step.subterm_internal site atSite
    have localDegree : subtree.degreeAt suffix=some l := by
      simpa only [LTerm.degreeAt,LTerm.subterm_append,atSite,Option.bind_some] using degree
    obtain ⟨result,atResult,localRest⟩ := ih atMiddle (fun q member => inside q (List.mem_cons_of_mem _ member))
    refine ⟨result,atResult,?_⟩
    simpa only [List.map_cons,List.drop_left] using RegionalHistory.cons localStep localDegree support localRest

/-- Build the actual global function-part projection for a reflected body
program, at the original contextual head. No row or endpoint is supplied. -/
theorem contextual_body_function_projection (head : BetaAt source p middle)
    (lookup : subtermAt source p=some (.app (.lam body) argument)) (program : BetaHistory ps body target) :
    ∃ (v : Term) (original : ParallelHistory source v),∃ _ordinary : Atomic original,
      Internal (p++[.fn]) original ∧
      original.derivation.paths=ps.map (fun q => (p++[.fn,.body])++q) ∧
      ∃ (w : Term) (G : List Path) (projected : ParallelHistory middle w) (last : ParallelStep G v w),
        Atomic projected ∧ StepProjection (singleContraction head) original projected last ∧
        projected.derivation.paths=ps.map (fun q => p++q) := by
  have atBody : subtermAt source (p++[.fn,.body])=some body := by
    rw [subtermAt_append,lookup]
    simp [subtermAt]
  obtain ⟨v,lifted,_⟩ := program.prefix_lift atBody
  obtain ⟨original,ordinary,paths⟩ := lifted.atomic
  have inside : Internal (p++[.fn]) original := by
    intro q member
    rw [paths] at member
    obtain ⟨r,_,equal⟩ := List.mem_map.mp member
    exact ⟨.body::r,by simpa only [List.append_assoc,List.singleton_append] using equal.symm⟩
  obtain ⟨w,G,projected,last,projectedAtomic,row⟩ := ordinary.function_projection head inside
  obtain ⟨qs,upper,lower⟩ := row.function_paths head ordinary projectedAtomic inside
  have same : qs=ps := mapped_prefix_paths_injective (p++[.fn,.body]) (upper.symm.trans paths)
  exact ⟨v,original,ordinary,inside,paths,w,G,projected,last,projectedAtomic,row,by simpa only [same] using lower⟩

/-- Consume the global projection through the genuine rule (iii), matching
the supplied actual tail by its entire ordered schedule. -/
theorem contextual_body_program_not_normal (head : BetaAt source p middle)
    (lookup : subtermAt source p=some (.app (.lam body) argument)) (program : BetaHistory ps body target)
    (tail : ParallelHistory middle final) (ordinary : Atomic tail)
    (paths : tail.derivation.paths=ps.map (fun q => p++q)) (positive : 0<ps.length) :
    ¬ExtractionNormal (.of (.cons (singleContraction head) tail) (.cons head ordinary)) := by
  intro normal
  obtain ⟨v,original,originalAtomic,inside,upper,w,G,projected,last,projectedAtomic,row,lower⟩ :=
    contextual_body_function_projection head lookup program
  have originalPositive : 0<original.length := by
    have lengths := congrArg List.length upper
    rw [originalAtomic.paths_length,List.length_map] at lengths
    omega
  have extraction := (RootExtraction.functionPart (R := head) original originalAtomic projected projectedAtomic
    last row originalPositive inside).step
  change ExtractionStep (ExtractionRun.of (.cons (singleContraction head) projected) (.cons head projectedAtomic))
    (ExtractionRun.of original originalAtomic) at extraction
  have same : ExtractionRun.of (.cons (singleContraction head) projected) (.cons head projectedAtomic)=
      ExtractionRun.of (.cons (singleContraction head) tail) (.cons head ordinary) := by
    apply ExtractionRun.ext_paths
    change p::projected.derivation.paths=p::tail.derivation.paths
    rw [lower,paths]
  rw [same] at extraction
  exact normal ⟨_,extraction⟩

/-- The body branch of the silent-head contradiction, at an arbitrary actual
contextual head. Actual internality is used only to project the full coloured
tail; Outside arguments and rule-(iii) source program are then proved. -/
theorem RegionalHistory.contextual_body_not_normal {body argument : LTerm}
    (regional : RegionalHistory (SourceRegion body) qs u v) (head : StepAt p t u)
    (initial : INIT t) (source : t.subterm p=some (.app beta (.lam alpha body) argument))
    (inside : ∀ q∈qs,∃ suffix,q=p++suffix)
    (tail : ParallelHistory u.erase v.erase) (ordinary : Atomic tail)
    (paths : tail.derivation.paths=qs) (positive : 0<qs.length) :
    ¬ExtractionNormal (.of (.cons (singleContraction head.betaAt) tail) (.cons head.betaAt ordinary)) := by
  obtain ⟨part,_,localHistory⟩ := regional.subterm_internal (head.contract_lookup source) inside
  have outside := initial_argument_outside_body_subregion (regionTerm := body) (initial.subterm source)
    (regionSite := []) (by simp [LTerm.subterm])
  obtain ⟨oldTarget,oldBodyHistory,_⟩ := localHistory.contract_body_reflect outside
  have back : (qs.map (List.drop p.length)).map (fun q => p++q)=qs := by
    rw [List.map_map]
    have per : ∀ q∈qs,((fun q => p++q) ∘ List.drop p.length) q=id q := by
      intro q member
      obtain ⟨suffix,equal⟩ := inside q member
      simp only [Function.comp_apply,equal,List.drop_left,id_eq]
    simpa only [List.map_id] using List.map_congr_left per
  have lookup : subtermAt t.erase p=some (.app (.lam body.erase) argument.erase) := by
    rw [←LTerm.erase_subterm,source]
    rfl
  exact contextual_body_program_not_normal head.betaAt lookup oldBodyHistory.betaHistory tail ordinary
    (paths.trans back.symm) (by simpa only [List.length_map] using positive)
end Lamping.Lambda.Labelled


