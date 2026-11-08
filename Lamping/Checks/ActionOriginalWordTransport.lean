import Lamping.Lamping.ActionOriginalWordTransport
import Lamping.Checks.Phase5Review.ActionCandidate
import Lamping.Checks.FamilyRepresentation

namespace Lamping.Checks.ActionOriginalWordTransportChecks
open AG Graph Lambda Lambda.Labelled

private def P : EdgeWord := [⟨7,false⟩,⟨11,true⟩]
private def A : EdgeWord := [⟨23,false⟩]
private def B : EdgeWord := [⟨29,true⟩]

private noncomputable def symmetricWeights {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W] (g : Net signature N B W)
    (seed : Endpoint g → EdgeWord) (e : Endpoint g) : EdgeWord :=
  seed e ++ EdgeWord.reverse (seed (g.wire e))

private theorem symmetric_reversal {N B W : Type}
    [FiniteNames N] [FiniteNames B] [FiniteNames W] (g : Net signature N B W)
    (seed : Endpoint g → EdgeWord) : OriginalWordReversal (symmetricWeights g seed) := by
  intro e
  simp only [symmetricWeights,Pairing.involutive,EdgeWord.reverse_append,EdgeWord.reverse_reverse]

namespace Fan
private abbrev site := Phase5Review.ActionCandidate.site
private def first : Endpoint site.net := .inl ⟨.inr (.inl ()),.inl ()⟩
private def body : Endpoint site.net := .inl ⟨.inr (.inr ()),.inr true⟩
private def exterior : Endpoint site.net := .inl ⟨.inl (),.inl ()⟩
private def principal : SiteActionPrincipal site where
  edges := [first,.inr (.inr (.inr (),true))]
  first := rfl
  last := rfl
  transparent := by
    intro e f member
    change (e,f)∈[(first,.inr (.inr (.inr (),true)))] at member
    have same := List.mem_singleton.mp member
    cases same
    exact ⟨.inr (),false,rfl,rfl⟩
private noncomputable def seed (e : Endpoint site.net) : EdgeWord := by
  classical
  exact if e=first then P else if e=body then B else if e=exterior then A else []
private noncomputable def weights := symmetricWeights site.net seed
private noncomputable abbrev fragmentCut : Net signature Unit (Unit⊕(Bool⊕Bool)) Empty := cutFragment site.net
  (pathPartition (Schema.fanAction .lam 0 1 (by decide)) Unit) site.closed
private def outsideFirst : Endpoint fragmentCut := .inl ⟨(),.inl ()⟩
private def outsideLast : Endpoint fragmentCut := .inr (.inl (.inr (.inr true)))
private def inside := fanCrossEdges (f:=Op.lam) (i:=0) (j:=1) false true
private def raw : List (PlugSegment fragmentCut (fanRight .lam 0 1)) :=
  .inl outsideFirst :: (inside.map Sum.inr ++ [.inl outsideLast])
private def old := principal.crossing site false true
private def canonical : ActionCanonicalBlocks site principal raw old :=
  ActionCanonicalBlocks.through (site:=site) (principal:=principal) inside
    [exterior,first,.inr (.inr (.inr (),true))]
    (ActionCanonicalLocal.fan (site:=site) (FanCanonicalLocal.cross (site:=site) (principal:=principal) false true))
    rfl (.single outsideLast)
private noncomputable def actual := raw.map (plugEnd fragmentCut.label (fanRight .lam 0 1).label)
private theorem actual_raw : actual.map (plugEnd fragmentCut.label (fanRight .lam 0 1).label).invFun=raw := by
  simp only [actual,List.map_map,Function.comp_def,Bij.left_inv]
  change raw.map id=raw
  exact List.map_id raw

theorem actual_nonzero_full_seam :
    P≠[] ∧ A≠[] ∧ B≠[] ∧ physicalOriginalWord weights principal.edges=P ∧
    physicalOriginalWord weights old=A++P++B ∧
    raw.flatMap (Sum.elim (fun outside => weights (site.outsideEnd outside))
      (actionRhsOriginalWord (.fan .lam 0 1 (by decide)) (physicalOriginalWord weights principal.edges)))=A++P++B ∧
    physicalOriginalWord (site.actionOriginalWordWeights (.fan .lam 0 1 (by decide)) principal weights) actual=
      A++P++B ∧
    OriginalWordReversal (site.actionOriginalWordWeights (.fan .lam 0 1 (by decide)) principal weights) := by
  have reversal : OriginalWordReversal weights := symmetric_reversal site.net seed
  have principalWord : physicalOriginalWord weights principal.edges=P := by
    change (seed first ++ EdgeWord.reverse (seed (.inr (.inr (.inr (),false))))) ++
      ((seed (.inr (.inr (.inr (),true))) ++ EdgeWord.reverse (seed (.inl ⟨.inr (.inr ()),.inl ()⟩))) ++ [])=P
    simp [seed,first,body,exterior,EdgeWord.reverse]
  have oldWord : physicalOriginalWord weights old=A++P++B := by
    change (seed exterior ++ EdgeWord.reverse (seed (.inl ⟨.inr (.inl ()),.inr false⟩))) ++
      ((seed first ++ EdgeWord.reverse (seed (.inr (.inr (.inr (),false))))) ++
      ((seed (.inr (.inr (.inr (),true))) ++ EdgeWord.reverse (seed (.inl ⟨.inr (.inr ()),.inl ()⟩))) ++
      ((seed body ++ EdgeWord.reverse (seed (.inl ⟨.inr (.inr ()),.inr false⟩))) ++ [])))=A++P++B
    simp [seed,first,body,exterior,EdgeWord.reverse,List.append_assoc,Sum.inr.injEq]
    intro impossible
    cases impossible
  have transported := canonical.original_word_transport site (.fan .lam 0 1 (by decide)) weights reversal
  have actualRelation : ActionCanonicalBlocks site principal
      (actual.map (plugEnd fragmentCut.label (fanRight .lam 0 1).label).invFun) old := by
    rw [actual_raw];exact canonical
  have actualTransport := actualRelation.original_word_transport_actual site (.fan .lam 0 1 (by decide)) weights reversal
  exact ⟨by decide,by decide,by decide,principalWord,oldWord,transported.trans oldWord,actualTransport.trans oldWord,
    site.action_original_word_reversal (.fan .lam 0 1 (by decide)) principal weights reversal⟩
end Fan

namespace Body
private abbrev site := actualContinuationSite
private def first : Endpoint site.net := .inl ⟨.inr (.inl ()),.inl ()⟩
private def body : Endpoint site.net := .inl ⟨.inr (.inr ()),.inr true⟩
private def principal : SiteActionPrincipal site where
  edges := [first,.inr (.inr (.inr (false,false),false)),
    .inr (.inr (.inr (false,true),true)),.inr (.inr (.inr (true,false),false)),
    .inr (.inr (.inr (true,true),true))]
  first := rfl
  last := rfl
  transparent := by
    intro e f member
    change (e,f)∈[(first,.inr (.inr (.inr (false,false),false))),
      (.inr (.inr (.inr (false,false),false)),.inr (.inr (.inr (false,true),true))),
      (.inr (.inr (.inr (false,true),true)),.inr (.inr (.inr (true,false),false))),
      (.inr (.inr (.inr (true,false),false)),.inr (.inr (.inr (true,true),true)))] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with member|member|member|member <;> cases member
    · exact ⟨.inr (false,false),true,rfl,rfl⟩
    · exact ⟨.inr (false,true),false,rfl,rfl⟩
    · exact ⟨.inr (true,false),true,rfl,rfl⟩
    · exact ⟨.inr (true,true),false,rfl,rfl⟩
private noncomputable def seed (e : Endpoint site.net) : EdgeWord := by
  classical
  exact if e=first then P else if e=body then B else []
private noncomputable def weights := symmetricWeights site.net seed

theorem actual_nonzero_body_padding :
    P≠[] ∧ B≠[] ∧ physicalOriginalWord weights principal.edges=P ∧ weights body=B ∧
    ∃ (source : RootAccess site.net (.inl ())) (target : RootAccess site.reduce (.inl ())),
      physicalOriginalWord (site.actionOriginalWordWeights (.cro .lam 0 1 (by decide)) principal weights) target.val=
        physicalOriginalWord weights source.val ∧
      OriginalWordReversal (site.actionOriginalWordWeights (.cro .lam 0 1 (by decide)) principal weights) := by
  have reversal : OriginalWordReversal weights := symmetric_reversal site.net seed
  have principalWord : physicalOriginalWord weights principal.edges=P := by
    have w0 : weights first=P := by
      change seed first ++ EdgeWord.reverse (seed (.inr (.inr (.inr (false,false),true))))=P
      simp [seed,first,body,EdgeWord.reverse]
    have w1 : weights (.inr (.inr (.inr (false,false),false)))=[] := by
      change seed (.inr (.inr (.inr (false,false),false))) ++
        EdgeWord.reverse (seed (.inr (.inr (.inr (false,true),false))))=[]
      simp [seed,first,body,EdgeWord.reverse]
    have w2 : weights (.inr (.inr (.inr (false,true),true)))=[] := by
      change seed (.inr (.inr (.inr (false,true),true))) ++
        EdgeWord.reverse (seed (.inr (.inr (.inr (true,false),true))))=[]
      simp [seed,first,body,EdgeWord.reverse]
    have w3 : weights (.inr (.inr (.inr (true,false),false)))=[] := by
      change seed (.inr (.inr (.inr (true,false),false))) ++
        EdgeWord.reverse (seed (.inr (.inr (.inr (true,true),false))))=[]
      simp [seed,first,body,EdgeWord.reverse]
    have w4 : weights (.inr (.inr (.inr (true,true),true)))=[] := by
      change seed (.inr (.inr (.inr (true,true),true))) ++
        EdgeWord.reverse (seed (.inl ⟨.inr (.inr ()),.inl ()⟩))=[]
      simp [seed,first,body,EdgeWord.reverse]
    simp only [physicalOriginalWord,principal,List.flatMap_cons,List.flatMap_nil,w0,w1,w2,w3,w4,
      List.append_nil]
  have bodyWord : weights body=B := by
    have noFirst : site.net.wire body≠first := by
      intro same
      have other := congrArg site.net.wire same
      rw [Pairing.involutive] at other
      change body=(.inr (.inr (.inr (false,false),true)) : Endpoint site.net) at other
      cases other
    have different : site.net.wire body≠body := site.net.wire.fixedPointFree body
    have bodyNeFirst : body≠first := by intro same;cases same
    simp only [weights,symmetricWeights,seed,if_neg bodyNeFirst,if_neg noFirst,if_neg different]
    simp only [ite_true,show EdgeWord.reverse ([] : EdgeWord)=[] from rfl,List.append_nil]
  obtain ⟨source,sourceWord,_⟩ := ReachableUnaryFixture.actual_source_lambda_access
  obtain ⟨target,targetWord,finish⟩ := ReachableUnaryFixture.actual_target_lambda_access
  obtain ⟨a,b,labels⟩ := target.property.1.1
  obtain ⟨flow⟩ := actualBetaSite.reduce_flowBalance SoundnessBetaAncestor.actualFlow
  have transported := site.cro_lambda_original_word_access
    (ReachableUnaryFixture.actualContinuationIso.flowBalance flow) (.inl ()) rfl
    ReachableUnaryFixture.actual_source_matches principal source target
    (sourceWord.trans targetWord.symm) finish labels weights reversal
  exact ⟨by decide,by decide,principalWord,bodyWord,source,target,transported,
    site.action_original_word_reversal (.cro .lam 0 1 (by decide)) principal weights reversal⟩
end Body


#print axioms Fan.actual_nonzero_full_seam
#print axioms Body.actual_nonzero_body_padding
end Lamping.Checks.ActionOriginalWordTransportChecks
