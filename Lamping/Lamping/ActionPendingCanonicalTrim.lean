import Lamping.Lamping.ActionCanonicalOutsideCut
import Lamping.Lamping.ActionPendingWords
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable {f : Op} {i j : Nat} {lt : i<j}
variable (site : PathSite (.croAction f i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction f i j lt) V) site.closed

/-- Trim only the two segments forced by the actual copied auxiliary terminal.
The preceding canonical prefix keeps its supplied principal and assignment. -/
theorem PendingRhsBlock.cro_aux_canonical_trim (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut (Schema.croAction f i j lt).right.net)} {a b : Context}
    (pending : PendingRhsBlock cut (Schema.croAction f i j lt).right.net raw a b)
    (first : Endpoint cut) (head : raw.head?=some (.inl first)) (q : Aux f)
    (finish : pending.inside.getLast?=some ((unaryRightCore .cro f (Bij.refl _) i (j-1)).wire
      (.inl ⟨.inl (),.inr q⟩))) :
    ∃ old, ActionCanonicalBlocks site principal pending.pre old ∧
      Labelling site.net old a pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      raw=pending.pre++[.inr (.inr (.inl (.inr q))),.inr (.inl ⟨.inr q,.inr ()⟩)] ∧
      Traversal i (.op .cro) (.inl ()) (.inr ()) pending.middle b ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old := by
  obtain ⟨entry,shape,rule⟩ := unaryRight_copied_aux_prefix .cro f (Bij.refl _)
    (Or.inr (Or.inl rfl)) i (j-1) q pending.enter pending.inside pending.middle b
    pending.insideLabels pending.insideHead finish
  obtain ⟨old,relation,labels,start,last⟩ := pending.prefixPath.action_canonical_lift site
    (.cro f i j lt) principal first pending.last (pending.prefixHead.trans head) pending.prefixLast
  have ending : site.outsideEnd pending.last=site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩) := by
    have wired := site.outsideEnd_wire pending.last
    rw [pending.arrival,entry] at wired
    have same := congrArg site.net.wire.mate wired
    simpa only [Pairing.involutive] using same
  have whole := pending.equation
  rw [shape] at whole
  have words := relation.word site pending.prefixPath
  have physical : accessWord site.reduce (raw.map (plugEnd _ _))=
      accessWord site.reduce (pending.pre.map (plugEnd _ _)) := by
    have nonempty : pending.pre≠[] := by
      intro empty
      have starts := pending.prefixHead.trans head
      rw [empty] at starts
      cases starts
    refine (congrArg (fun es => accessWord site.reduce (es.map (plugEnd _ _))) whole).trans ?_
    cases preEq : pending.pre with
    | nil => exact False.elim (nonempty preEq)
    | cons e es =>
      simp only [List.cons_append,List.map_cons,List.map_append,accessWord,
        List.flatMap_append,List.map_nil,List.map_cons,List.flatMap_cons,List.flatMap_nil]
      have token (e : Endpoint (Schema.croAction f i j lt).right.net) :
          arrivalWord site.reduce ((plugEnd (cut).label (Schema.croAction f i j lt).right.net.label) (.inr e))=
            arrivalWord (Schema.croAction f i j lt).right.net e :=
        arrivalWord_plugRight cut (Schema.croAction f i j lt).right.net e
      rw [token,token]
      change _++([]++([]++[]))= _
      exact List.append_nil _
  refine ⟨old,relation,labels,start,?_,whole,rule,physical.trans words⟩
  rw [←ending]
  exact last
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable {f : Op} {i j : Nat} {lt : i<j}
variable (site : PathSite (.braAction f i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction f i j lt) V) site.closed

/-- The corresponding actual bra-action pending auxiliary trim. -/
theorem PendingRhsBlock.bra_aux_canonical_trim (principal : SiteActionPrincipal site)
    {raw : List (PlugSegment cut (Schema.braAction f i j lt).right.net)} {a b : Context}
    (pending : PendingRhsBlock cut (Schema.braAction f i j lt).right.net raw a b)
    (first : Endpoint cut) (head : raw.head?=some (.inl first)) (q : Aux f)
    (finish : pending.inside.getLast?=some ((unaryRightCore .bra f (Bij.refl _) i (j+1)).wire
      (.inl ⟨.inl (),.inr q⟩))) :
    ∃ old, ActionCanonicalBlocks site principal pending.pre old ∧
      Labelling site.net old a pending.middle ∧
      old.head?=some (site.outsideEnd first) ∧
      old.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩)) ∧
      raw=pending.pre++[.inr (.inr (.inl (.inr q))),.inr (.inl ⟨.inr q,.inr ()⟩)] ∧
      Traversal i (.op .bra) (.inl ()) (.inr ()) pending.middle b ∧
      accessWord site.reduce (raw.map (plugEnd _ _))=accessWord site.net old := by
  obtain ⟨entry,shape,rule⟩ := unaryRight_copied_aux_prefix .bra f (Bij.refl _)
    (Or.inr (Or.inr rfl)) i (j+1) q pending.enter pending.inside pending.middle b
    pending.insideLabels pending.insideHead finish
  obtain ⟨old,relation,labels,start,last⟩ := pending.prefixPath.action_canonical_lift site
    (.bra f i j lt) principal first pending.last (pending.prefixHead.trans head) pending.prefixLast
  have ending : site.outsideEnd pending.last=site.net.wire (.inl ⟨.inr (.inr ()),.inr q⟩) := by
    have wired := site.outsideEnd_wire pending.last
    rw [pending.arrival,entry] at wired
    have same := congrArg site.net.wire.mate wired
    simpa only [Pairing.involutive] using same
  have whole := pending.equation
  rw [shape] at whole
  have words := relation.word site pending.prefixPath
  have physical : accessWord site.reduce (raw.map (plugEnd _ _))=
      accessWord site.reduce (pending.pre.map (plugEnd _ _)) := by
    have nonempty : pending.pre≠[] := by
      intro empty
      have starts := pending.prefixHead.trans head
      rw [empty] at starts
      cases starts
    refine (congrArg (fun es => accessWord site.reduce (es.map (plugEnd _ _))) whole).trans ?_
    cases preEq : pending.pre with
    | nil => exact False.elim (nonempty preEq)
    | cons e es =>
      simp only [List.cons_append,List.map_cons,List.map_append,accessWord,
        List.flatMap_append,List.map_nil,List.map_cons,List.flatMap_cons,List.flatMap_nil]
      have token (e : Endpoint (Schema.braAction f i j lt).right.net) :
          arrivalWord site.reduce ((plugEnd (cut).label (Schema.braAction f i j lt).right.net.label) (.inr e))=
            arrivalWord (Schema.braAction f i j lt).right.net e :=
        arrivalWord_plugRight cut (Schema.braAction f i j lt).right.net e
      rw [token,token]
      change _++([]++([]++[]))= _
      exact List.append_nil _
  refine ⟨old,relation,labels,start,?_,whole,rule,physical.trans words⟩
  rw [←ending]
  exact last
end
end Lamping.AG
