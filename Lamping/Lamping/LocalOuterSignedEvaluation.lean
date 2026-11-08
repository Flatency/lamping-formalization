import Lamping.Lamping.SourceRouteEvaluation
import Lamping.Lambda.UniformOldOuterImageAlignment

namespace Lamping.Lambda.Marked
open Labelled

private theorem uniform_signed_sourceWord (s : Nat → Label) (alpha : Label) :
    ∀ (label : Label),label.OuterBarsSafe (fun d=>d.relabel s=alpha) →
      label.sourceWord (fun n=>(s n).edgeWord) alpha.edgeWord (EdgeWord.reverse alpha.edgeWord)=
        (label.relabel s).edgeWord
  | .single (.atom _),_ => rfl
  | .single (.over payload),safe => by
    change alpha.edgeWord=(payload.relabel s).edgeWord
    rw [safe]
  | .single (.under payload),safe => by
    change EdgeWord.reverse alpha.edgeWord=EdgeWord.reverse (payload.relabel s).edgeWord
    rw [safe]
  | .cons (.atom _) rest,safe => by
    simp only [Label.sourceWord,Letter.sourceWord,Label.relabel,Letter.relabel,Label.edgeWord_concat]
    rw [uniform_signed_sourceWord s alpha rest safe]
  | .cons (.over _) rest,safe => by
    simp only [Label.sourceWord,Letter.sourceWord,Label.relabel,Letter.relabel,Label.edgeWord_concat,
      Label.edgeWord_over]
    rw [safe.1,uniform_signed_sourceWord s alpha rest safe.2]
  | .cons (.under _) rest,safe => by
    simp only [Label.sourceWord,Letter.sourceWord,Label.relabel,Letter.relabel,Label.edgeWord_concat,
      Label.edgeWord_under]
    rw [safe.1,uniform_signed_sourceWord s alpha rest safe.2]

theorem RelativeOldHistory.local_outer_signed_evaluation
    {source target localTarget localNode : LTerm}
    {F ps : List Path} {endpoint : Marked} {alpha : Label} {p : Path}
    (old : RelativeOldHistory F ps (mark F source.erase) endpoint)
    (global : Labelled.History ps source target)
    (localHistory : Labelled.History ps (initLabels source.erase) localTarget)
    (selected : ∀ name∈F,source.degreeAt name=some alpha)
    (atLocal : localTarget.subterm p=some localNode) :
    ∃ node,target.subterm p=some node ∧
      localNode.label.sourceWord
        (fun n => (initialRelabelling source 0 n).edgeWord)
        alpha.edgeWord (EdgeWord.reverse alpha.edgeWord)=node.label.edgeWord := by
  have transported := localHistory.relabel (initialRelabelling source 0)
  have factor : (initLabels source.erase).relabel (initialRelabelling source 0)=source :=
    initialRelabelling_factor source 0
  rw [factor] at transported
  have whole := transported.deterministic global
  have bars : localNode.label.OuterBarsSafe
      (fun d=>d.relabel (initialRelabelling source 0)=alpha) :=
    (LTerm.outerBarsSafe_iff _ _).mp (old.local_outer_image_bars localHistory selected)
      _ (LTerm.label_mem_of_subterm atLocal)
  refine ⟨localNode.relabel (initialRelabelling source 0),?_,?_⟩
  · rw [←whole,LTerm.subterm_relabel,atLocal]
    rfl
  · have equation := uniform_signed_sourceWord (initialRelabelling source 0) alpha localNode.label bars
    cases localNode <;> exact equation

#print axioms RelativeOldHistory.local_outer_signed_evaluation
end Lamping.Lambda.Marked
