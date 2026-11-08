import Lamping.Lamping.CoarseTrueWritingRoles
import Lamping.Lambda.UniformOldOuterImageAlignment
import Lamping.Lamping.ActualUnsafeMarkerLeaves
namespace Lamping.AG
open Graph Lambda Lambda.Labelled


private theorem relabel_safe_iff_tags_zero
    {s : Nat→Label} {region : Nat→Prop} {degree : Label}
    (images : ∀n,region n→(s n).OuterBarsSafe (fun d=>d≠degree)) :
    ∀label : Label,label.Supported region→
      label.OuterBarsSafe (fun d=>d.relabel s=degree)→
      ((label.relabel s).OuterBarsSafe (fun d=>d≠degree) ↔
        ∀tag∈label.letters.map coarseLetterTag,tag=0)
  | .single (.atom n),support,_bars => by
    simp [Label.relabel,Letter.relabel,Label.letters,coarseLetterTag,images n support]
  | .single (.over d),_support,bars => by
    simp_all [Label.relabel,Letter.relabel,Label.over,Label.OuterBarsSafe,Label.letters,coarseLetterTag]
  | .single (.under d),_support,bars => by
    simp_all [Label.relabel,Letter.relabel,Label.under,Label.OuterBarsSafe,Label.letters,coarseLetterTag]
  | .cons (.atom n) rest,support,bars => by
    simpa [Label.relabel,Letter.relabel,Label.outerBarsSafe_concat,Label.letters,coarseLetterTag,
      images n support.1] using relabel_safe_iff_tags_zero images rest support.2 bars
  | .cons (.over d) rest,_support,bars => by
    simp_all [Label.relabel,Letter.relabel,Label.over,Label.outerBarsSafe_concat,
      Label.OuterBarsSafe,Label.letters,coarseLetterTag]
  | .cons (.under d) rest,_support,bars => by
    simp_all [Label.relabel,Letter.relabel,Label.under,Label.outerBarsSafe_concat,
      Label.OuterBarsSafe,Label.letters,coarseLetterTag]

theorem EvaluatedChainResiduals.degree_read_safety_of_target_images
    {K B W V : Type}
    [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
    {kept : K → Graph.Label signature} {i : Nat}
    (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
    {root : B} {source target localTarget : LTerm}
    {F ps : List Path} {degree : Label} {marked oldEndpoint : Marked}
    {edge : BetaEdge site.net}
    {selection : SourceEdgeSelection (initLabels source.erase) site.net root}
    {targetSelection : OccurrenceFragmentSelection target site.reduce root}
    {ls rs : Path} {les res : List Path}
    {leftChain : PrerequisiteChain target ls les}
    {rightChain : PrerequisiteChain target rs res}
    (matching : Matches site.net root source.erase)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (positive : boundary root=true)
    (relative : Marked.RelativeHistory ps
      (Marked.mark (site.betaSyntaxFiber root source.erase) source.erase) marked)
    (normal : Marked.Normal marked)
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) oldEndpoint)
    (history : History ps source target)
    (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun payload=>payload≠degree))
    (localHistory : History ps (initLabels source.erase) localTarget)
    (geometry : SiteBetaGeometry site edge)
    (left : EvaluatedChainResiduals site (localTarget:=localTarget)
      edge selection targetSelection leftChain)
    (right : EvaluatedChainResiduals site (localTarget:=localTarget)
      edge selection targetSelection rightChain)
    (same : SameChainRepresentation targetSelection leftChain rightChain) :
    ∀ (ordinal : Nat) (lm : {p : Path //p∈les}) (rm : {p : Path //p∈res}),
      les[ordinal]?=some lm.val →res[ordinal]?=some rm.val →
      (degreeReadSafe degree (target.labelAt lm.val) ↔
        degreeReadSafe degree (target.labelAt rm.val)) := by
  let s := initialRelabelling source 0
  let region : Nat→Prop := fun n=>Label.atom n∈(initLabels source.erase).labels
  have images (n : Nat) (inside : region n) : (s n).OuterBarsSafe (fun d=>d≠degree) := by
    apply (LTerm.outerBarsSafe_iff _ _).mp sourceSafe
    apply initialRelabelling_mem source 0 n (Nat.zero_le n)
    simpa only [Nat.zero_add] using LTerm.basis_atom_bound source inside
  have supported := localHistory.supported (init_is_INIT source.erase).supported
  have bars := old.local_outer_image_bars localHistory selected
  have transported := localHistory.relabel s
  rw [show (initLabels source.erase).relabel s=source from initialRelabelling_factor source 0] at transported
  have whole : localTarget.relabel s=target := transported.deterministic history
  have atSafety {start : Path} {es : List Path} {chain : PrerequisiteChain target start es}
      (out : EvaluatedChainResiduals site (localTarget:=localTarget) edge selection targetSelection chain)
      (member : {p : Path //p∈es}) :
      degreeReadSafe degree (target.labelAt member.val) ↔
        ∀tag∈(out.node member).label.letters.map coarseLetterTag,tag=0 := by
    have memberLabel := LTerm.label_mem_of_subterm (out.lookup member)
    have safeIff := relabel_safe_iff_tags_zero images (out.node member).label
      ((LTerm.supported_iff _ _).mp supported _ memberLabel)
      ((LTerm.outerBarsSafe_iff _ _).mp bars _ memberLabel)
    have actual : target.labelAt member.val=some ((out.node member).label.relabel s) := by
      have samePath := congrArg (fun term : LTerm=>term.labelAt member.val) whole
      symm
      simpa only [LTerm.labelAt,LTerm.subterm_relabel,out.lookup member,Option.map_some,LTerm.label_relabel] using samePath

    simpa [degreeReadSafe,actual] using safeIff
  have profiles := left.coarse_true_role_profiles site matching flow positive relative normal localHistory geometry right same
  intro ordinal lm rm leftAt rightAt
  have lb : ordinal<les.attach.length := by simpa using (List.getElem?_eq_some_iff.mp leftAt).1
  have rb : ordinal<res.attach.length := by simpa using (List.getElem?_eq_some_iff.mp rightAt).1
  have le : les.attach[ordinal]=lm := by
    apply Subtype.ext
    simpa only [List.getElem_attach] using (List.getElem?_eq_some_iff.mp leftAt).2
  have re : res.attach[ordinal]=rm := by
    apply Subtype.ext
    simpa only [List.getElem_attach] using (List.getElem?_eq_some_iff.mp rightAt).2
  have tags : (left.node lm).label.letters.map coarseLetterTag=
      (right.node rm).label.letters.map coarseLetterTag := by
    have slot := congrArg (fun xs : List (List Nat)=>xs[ordinal]?) profiles
    simpa only [List.getElem?_map,List.getElem?_eq_getElem lb,List.getElem?_eq_getElem rb,
      Option.map_some,Option.some.injEq,le,re] using slot
  rw [atSafety left lm,atSafety right rm,tags]

#print axioms EvaluatedChainResiduals.degree_read_safety_of_target_images

end Lamping.AG

