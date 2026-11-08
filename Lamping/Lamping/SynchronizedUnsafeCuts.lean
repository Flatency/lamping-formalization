import Lamping.Lamping.DegreeReadSafetyProfiles
import Lamping.Lamping.ActualCurrentAfterChains
namespace Lamping.AG
open Graph Lambda Lambda.Labelled


private theorem scan_bad {A B : Type} (P : A→Prop) (Q : B→Prop)
    (xs : List A) (ys : List B) (length : xs.length=ys.length)
    (sync : ∀ (n : Nat) x y,xs[n]?=some x→ys[n]?=some y→(P x↔Q y)) :
    ((∀x∈xs,P x) ∧(∀y∈ys,Q y)) ∨
    ∃bs e after cs f rest,xs=bs++e::after ∧ys=cs++f::rest ∧
      bs.length=cs.length ∧(∀x∈bs,P x) ∧(∀y∈cs,Q y) ∧¬P e ∧¬Q f := by
  classical
  induction xs generalizing ys with
  | nil =>
    have empty : ys=[] := List.length_eq_zero_iff.mp length.symm
    subst ys;exact Or.inl ⟨by simp,by simp⟩
  | cons x xs ih =>
    cases ys with
    | nil => simp at length
    | cons y ys =>
      have head := sync 0 x y rfl rfl
      have tail : ∀ (n : Nat) x y,xs[n]?=some x→ys[n]?=some y→(P x↔Q y) := by
        intro n a b atLeft atRight
        exact sync (n+1) a b atLeft atRight
      by_cases good : P x
      · have rightGood := head.mp good
        rcases ih ys (by simpa using length) tail with safe | bad
        · exact Or.inl ⟨by simpa using And.intro good safe.1,by simpa using And.intro rightGood safe.2⟩
        · obtain ⟨bs,e,after,cs,f,rest,ls,rs,len,lp,rp,lb,rb⟩ := bad
          refine Or.inr ⟨x::bs,e,after,y::cs,f,rest,by rw [ls];rfl,by rw [rs];rfl,by simpa using len,?_,?_,lb,rb⟩
          · intro z member;rcases List.mem_cons.mp member with rfl | inside
            · exact good
            · exact lp z inside
          · intro z member;rcases List.mem_cons.mp member with rfl | inside
            · exact rightGood
            · exact rp z inside
      · exact Or.inr ⟨[],x,xs,[],y,ys,rfl,rfl,rfl,by simp,by simp,good,fun h=>good (head.mpr h)⟩

private theorem cut_at_split
    {F ps : List Path} {source target : LTerm} {degree : Label} {endpoint : Marked}
    (old : Marked.RelativeOldHistory F ps (Marked.mark F source.erase) endpoint)
    (history : History ps source target) (selected : ∀name∈F,source.degreeAt name=some degree)
    (sourceSafe : source.OuterBarsSafe (fun d=>d≠degree))
    (chain : PrerequisiteChain target start edges) (split : edges=before++edge::after)
    (safe : ∀p∈before,degreeReadSafe degree (target.labelAt p))
    (bad : ¬degreeReadSafe degree (target.labelAt edge)) :
    ∃cut : ActualUnsafeMarkerCut F ps source target degree start edges,
      cut.before=before ∧cut.edge=edge ∧cut.after=after := by
  have member : edge∈edges := by rw [split];exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨bs,rest,reader,actualSplit,segment,remaining,read⟩ := chain.split_at_member member
  obtain ⟨front,back⟩ := chain.first_created_split_unique split actualSplit
  subst bs;subst rest
  have nodeExists : ∃node,target.subterm edge=some node := by
    rcases remaining.eligible List.mem_cons_self with ⟨parent,beta,fn,arg,eq,lookup⟩ | ⟨stamp,body,lookup⟩
    · refine ⟨fn,?_⟩
      rw [eq,LTerm.subterm_append,lookup];cases fn <;> rfl
    · exact ⟨_,lookup⟩
  obtain ⟨node,lookup⟩ := nodeExists
  have markedNode : ¬node.label.OuterBarsSafe (fun d=>d≠degree) := by
    intro good
    apply bad
    simpa only [degreeReadSafe,LTerm.labelAt,lookup,Option.map_some,Option.some.injEq,forall_eq'] using good
  have safeLabels : ∀p∈before,∀n,target.subterm p=some n→n.label.OuterBarsSafe (fun d=>d≠degree) := by
    intro p member n atNode
    exact safe p member n.label (by simp only [LTerm.labelAt,atNode,Option.map_some])
  obtain ⟨forward,reading⟩ : ∃forward,PrerequisiteReadsDirected target reader edge forward := by
    rcases read with ⟨stamp,fn,arg,atReader,eq⟩ | ⟨stamp,body,atReader,eq⟩
    · exact ⟨true,Or.inl ⟨stamp,fn,arg,atReader,eq⟩,eq⟩
    · exact ⟨false,Or.inr ⟨stamp,body,atReader,eq⟩,eq⟩
  have spine := old.directed_marker_spine history selected sourceSafe segment reading lookup markedNode safeLabels
  let cut : ActualUnsafeMarkerCut F ps source target degree start edges :=
    ⟨before,edge,after,reader,node,forward,split,segment,remaining,reading,lookup,safe,markedNode,spine,spine.leaf_output lookup⟩
  exact ⟨cut,rfl,rfl,rfl⟩

theorem EvaluatedChainResiduals.synchronized_unsafe_cuts_of_target_images
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
    ((∀e∈les,degreeReadSafe degree (target.labelAt e)) ∧
      (∀e∈res,degreeReadSafe degree (target.labelAt e))) ∨
    ∃ordinal : Nat,
      ∃leftCut : ActualUnsafeMarkerCut F ps source target degree ls les,
      ∃rightCut : ActualUnsafeMarkerCut F ps source target degree rs res,
        leftCut.before.length=ordinal ∧rightCut.before.length=ordinal ∧
        les.take ordinal=leftCut.before ∧res.take ordinal=rightCut.before ∧
        les[ordinal]?=some leftCut.edge ∧res[ordinal]?=some rightCut.edge ∧
        les.drop (ordinal+1)=leftCut.after ∧res.drop (ordinal+1)=rightCut.after ∧
        ¬degreeReadSafe degree (target.labelAt leftCut.edge) ∧
        ¬degreeReadSafe degree (target.labelAt rightCut.edge) ∧
        leftCut.after.length<les.length ∧rightCut.after.length<res.length := by
  have sync := left.degree_read_safety_of_target_images site matching flow positive relative normal
    old history selected sourceSafe localHistory geometry right same
  have lengths : les.length=res.length := by
    have length := congrArg List.length same
    simpa only [SameChainRepresentation,canonicalChainImage_length] using length
  have aligned : ∀(ordinal : Nat) l r,les[ordinal]?=some l→res[ordinal]?=some r→
      (degreeReadSafe degree (target.labelAt l) ↔degreeReadSafe degree (target.labelAt r)) := by
    intro ordinal l r atLeft atRight
    exact sync ordinal ⟨l,List.mem_of_getElem? atLeft⟩ ⟨r,List.mem_of_getElem? atRight⟩ atLeft atRight
  rcases scan_bad (fun e=>degreeReadSafe degree (target.labelAt e))
      (fun e=>degreeReadSafe degree (target.labelAt e)) les res lengths aligned with safe | bad
  · exact Or.inl safe
  · obtain ⟨bs,e,after,cs,f,rest,leftSplit,rightSplit,len,leftSafe,rightSafe,leftBad,rightBad⟩ := bad
    obtain ⟨lc,lb,le,la⟩ := cut_at_split old history selected sourceSafe leftChain leftSplit leftSafe leftBad
    obtain ⟨rc,rb,re,ra⟩ := cut_at_split old history selected sourceSafe rightChain rightSplit rightSafe rightBad
    refine Or.inr ⟨bs.length,lc,rc,by rw [lb],by rw [rb,←len],?_,?_,?_,?_,?_,?_,?_,?_,lc.after_length_lt,rc.after_length_lt⟩
    · simp [leftSplit,lb]
    · simp [rightSplit,rb,len]
    · simp [leftSplit,le]
    · simp [rightSplit,re,len]
    · simp [leftSplit,la]
    · simp [rightSplit,ra,len]
    · simpa only [le] using leftBad
    · simpa only [re] using rightBad

#print axioms EvaluatedChainResiduals.synchronized_unsafe_cuts_of_target_images

end Lamping.AG


