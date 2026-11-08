/-
Actual occurrence cuts with a copied lambda parent and copied binding end.
The padding assignment and both literal cuts are constructed from supplied
RootAccess/fragment data. Fixed writer/reader pieces are removed at their
actual ordinals; no desired normalized piece or path completion is assumed.
This module does not prove whole target-fragment equality or Joint.
-/
import Lamping.Lamping.ActionLambdaCanonicalAccess
import Lamping.Lamping.ActionCopiedLambdaBodyPrefixes
import Lamping.Lamping.CorridorBoundaryTurns
namespace Lamping.AG
open Graph
private theorem lam_body_input {kind : Kind} {index : Nat} {p q : Port kind} {a b : Context}
    (shape : kind=.op .lam) (bodyRole : HEq q lamBody)
    (rule : Traversal index kind p q a b) :
    HEq p (Sum.inl () : Port (.op .lam)) ∧a=b := by
  subst kind
  have qEq : q=lamBody := eq_of_heq bodyRole
  subst q
  cases rule with
  | direct passage => cases passage;exact ⟨HEq.rfl,rfl⟩
  | inverse passage => cases passage

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem Labelling.lambda_body_padding_parent (node : N) (ctx body : Port (g.label node).sort)
    (shape : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (bodyRole : HEq body lamBody)
    {before : List (Endpoint g)} {a b : Context}
    (labels : Labelling g (before++[.inl ⟨node,body⟩]) a b) (nonempty : before≠[]) :
    before.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) := by
  obtain ⟨initial,previous,middle,split,prefixLabels,turn⟩ := labels.last_turn nonempty
  generalize previousEq : g.wire previous=arrival at turn
  cases turn with
  | node n p q rule =>
    have input := lam_body_input shape bodyRole rule
    have pEq : p=ctx := eq_of_heq (input.1.trans ctxRole.symm)
    subst p
    have prev : previous=g.wire (.inl ⟨node,ctx⟩) := by
      have wired := congrArg g.wire previousEq
      simpa only [Pairing.involutive] using wired
    rw [split,List.getLast?_concat,prev]
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.lam i j lt) V) site.closed
private abbrev croBodyRight (i j : Nat) (lt : i<j) := (Schema.croAction .lam i j lt).right.net
local notation "rhs" => croBodyRight i j lt
 theorem PathSite.cro_lambda_padding_labels
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    Labelling site.net (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) a (InitialOffsets.croAt i b) ∧
      source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      PlugLabelling cut rhs (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.croAt i b) := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut rhs first actualHead
    (.inl ()) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  have intended := site.cro_lambda_canonical_access flow root positive matching principal source target word finish labels
  obtain ⟨old,actual,oldLabels,_,_,padded⟩ := pending.cro_lambda_canonical_completion site principal first rawHead insideFinish
  have oldEq := actual.fixed_source_unique site intended
  rw [oldEq] at oldLabels
  refine ⟨oldLabels,?_,padded.labelling⟩
  apply Labelling.lambda_body_padding_parent (g:=site.net) (.inr (.inr ())) (.inl ()) (.inr true) rfl HEq.rfl HEq.rfl oldLabels
  intro empty
  have head := source.property.2.1
  rw [empty] at head
  cases head
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.lam i j lt) V) site.closed
private abbrev braBodyRight (i j : Nat) (lt : i<j) := (Schema.braAction .lam i j lt).right.net
local notation "rhs" => braBodyRight i j lt
 theorem PathSite.bra_lambda_padding_labels
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    Labelling site.net (source.val++[.inl ⟨.inr (.inr ()),.inr true⟩]) a (InitialOffsets.braAt i b) ∧
      source.val.getLast?=some (site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) ∧
      PlugLabelling cut rhs (target.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))]) a (InitialOffsets.braAt i b) := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  have actualHead : target.val.head?=some (AG.plugLeft cut rhs first) := target.property.2.1
  obtain ⟨pending,insideFinish⟩ := labels.pending_new_node cut rhs first actualHead
    (.inl ()) (.inl ()) finish
  have rawHead : (target.val.map (plugEnd (cut).label (rhs).label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,actualHead]
    exact congrArg some ((plugEnd (cut).label (rhs).label).left_inv (.inl first))
  have intended := site.bra_lambda_canonical_access flow root positive matching principal source target word finish labels
  obtain ⟨old,actual,oldLabels,_,_,padded⟩ := pending.bra_lambda_canonical_completion site principal first rawHead insideFinish
  have oldEq := actual.fixed_source_unique site intended
  rw [oldEq] at oldLabels
  refine ⟨oldLabels,?_,padded.labelling⟩
  apply Labelling.lambda_body_padding_parent (g:=site.net) (.inr (.inr ())) (.inl ()) (.inr true) rfl HEq.rfl HEq.rfl oldLabels
  intro empty
  have head := source.property.2.1
  rw [empty] at head
  cases head
end
end Lamping.AG
namespace Lamping.AG
theorem trim_after_literal_pivot {X : Type} (initial suffix trimmed : List X) (pivot entry last : X)
    (literal : (initial++[pivot])++suffix=trimmed++[entry,last])
    (notEntry : pivot≠entry) (notLast : pivot≠last) :
    ∃middle,trimmed=(initial++[pivot])++middle ∧suffix=middle++[entry,last] := by
  rcases List.append_eq_append_iff.mp literal with ⟨extra,headEq,tailEq⟩|⟨extra,headEq,tailEq⟩
  · exact ⟨extra,headEq,tailEq⟩
  · cases extra with
    | nil => exact ⟨[],by simpa only [List.append_nil] using headEq.symm,by simpa only [List.nil_append] using tailEq.symm⟩
    | cons x xs =>
      have first : entry=x := (List.cons.inj tailEq).1
      cases xs with
      | nil =>
        have ends := congrArg List.getLast? headEq
        simp only [List.getLast?_concat] at ends
        exact False.elim (notEntry ((Option.some.inj ends).trans first.symm))
      | cons y ys =>
        have rest : [last]=(y::ys)++suffix := (List.cons.inj tailEq).2
        have second : last=y := (List.cons.inj rest).1
        have lengthEq := congrArg List.length rest
        simp only [List.length_nil,List.length_append,List.length_cons] at lengthEq
        have empty : ys=[] := List.length_eq_zero_iff.mp (by omega)
        subst ys
        have ends := congrArg List.getLast? headEq
        simp only [List.getLast?_append,List.getLast?_cons,Option.some_or] at ends
        exact False.elim (notLast ((Option.some.inj ends).trans second.symm))
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.croAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.croAction Op.lam i j lt) V) site.closed
local notation "rhs" => croBodyRight i j lt
 theorem SourceEdgeFragment.cro_copied_binding_piece_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.body])
    (targetWord : position=accessWord site.reduce targetParent.val++[.body])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr false⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃tail oldTail seam output,
      source.segments=.inl ⟨.inr (.inr ()),.inr true⟩::oldTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
          .inl (.inr (.inl (.inr (.inr true))))::(tail++
            [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr ()⟩)]) ∧
      ActionCanonicalBlocks site principal (.inl (.inr (.inl (.inr (.inr true))))::tail) source.segments ∧
      PlugLabelling cut rhs (.inl (.inr (.inl (.inr (.inr true))))::tail) seam output := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩|labels
    · have head:=targetParent.property.2.1;rw [empty] at head;cases head
    · exact labels
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val := by
    have same := sourceWord.symm.trans targetWord
    exact List.append_cancel_right same
  obtain ⟨padLabels,sourceFinish,paddedLabels⟩ := site.cro_lambda_padding_labels flow root positive sourceMatches
    principal sourceParent targetParent parentWord parentFinish parentLabels
  have parentRelation := site.cro_lambda_canonical_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have fromEndpoint := actual_lambda_child_head sourceMatches source role sourceParent sourceWord
    (.inr (.inr ())) (.inl ()) (.inr true) HEq.rfl sourceFinish
  have sourceHead := source.start
  rw [fromEndpoint] at sourceHead
  obtain ⟨oldTail,sourcePiece⟩ := List.head?_eq_some_iff.mp sourceHead
  obtain ⟨fullTail,writerMiddle,targetPiece,writer,suffix⟩ := unary_copied_lambda_body_fragment cut .cro
    (Bij.refl Unit) (Or.inl rfl) i (j-1) (current:=current) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at fullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
      .inl (.inr (.inl (.inr (.inr true))))::fullTail at targetPiece
  obtain ⟨pending,whole,oldLabels,_oldEnd,trimmed⟩ := site.cro_aux_canonical_access
    flow root positive sourceMatches principal source.access target.access (source.word.trans target.word.symm)
    false endAt wholeLabels
  have untrimmed : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
      [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))])++fullTail=pending.pre++
          [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr ()⟩)] := by
    rw [←trimmed,targetCut.2,List.map_append,targetPiece]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  obtain ⟨tail,trimmedSplit,tailEq⟩ := trim_after_literal_pivot
    (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
      [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩)])
    fullTail pending.pre (.inl (.inr (.inl (.inr (.inr true)))))
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr ()⟩))
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using untrimmed)
    (by intro h;cases h) (by intro h;cases h)
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have oldSplit : source.access.val=(sourceParent.val++[.inl ⟨.inr (.inr ()),.inr true⟩])++oldTail := by
    rw [sourceCut.2,sourcePiece]
    simp only [List.append_assoc,List.singleton_append]
  have rawSplit : pending.pre=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])++tail := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using trimmedSplit
  have parentLast : (sourceParent.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).getLast?=
      some (site.outsideEnd (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
    rfl
  obtain ⟨seam,relation,actualLabels⟩ := whole.unary_cut_at_actual_prefix site (by intro h;cases h)
    parentRelation pending.prefixPath.labelling paddedLabels oldSplit rawSplit
    (.inr (.inl (.inr (.inr true)))) parentLast
  refine ⟨tail,oldTail,seam,pending.middle,sourcePiece,?_,?_,actualLabels⟩
  · simpa only [tailEq] using targetPiece
  · simpa only [sourcePiece] using relation
end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (Schema.braAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.braAction Op.lam i j lt) V) site.closed
local notation "rhs" => braBodyRight i j lt
 theorem SourceEdgeFragment.bra_copied_binding_piece_cut
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    (role : SourceDeparture parentTerm .body edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[.body])
    (targetWord : position=accessWord site.reduce targetParent.val++[.body])
    (parentFinish : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)))
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl ()),.inr false⟩)))
    {a b : Context} (wholeLabels : Labelling site.reduce target.access.val a b) :
    ∃tail oldTail seam output,
      source.segments=.inl ⟨.inr (.inr ()),.inr true⟩::oldTail ∧
      target.segments.map (plugEnd (cut).label (rhs).label).invFun=
        .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
          .inl (.inr (.inl (.inr (.inr true))))::(tail++
            [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr ()⟩)]) ∧
      ActionCanonicalBlocks site principal (.inl (.inr (.inl (.inr (.inr true))))::tail) source.segments ∧
      PlugLabelling cut rhs (.inl (.inr (.inl (.inr (.inr true))))::tail) seam output := by
  have targetCut := target.child_prefix targetMatches role targetParent targetWord
  obtain ⟨middle,assignment,pieceLabels⟩ := target.assignments a b wholeLabels
  rw [targetCut.1] at assignment
  have parentLabels : Labelling site.reduce targetParent.val a middle := by
    rcases assignment with ⟨empty,_⟩|labels
    · have head:=targetParent.property.2.1;rw [empty] at head;cases head
    · exact labels
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val := by
    have same := sourceWord.symm.trans targetWord
    exact List.append_cancel_right same
  obtain ⟨padLabels,sourceFinish,paddedLabels⟩ := site.bra_lambda_padding_labels flow root positive sourceMatches
    principal sourceParent targetParent parentWord parentFinish parentLabels
  have parentRelation := site.bra_lambda_canonical_access flow root positive sourceMatches principal
    sourceParent targetParent parentWord parentFinish parentLabels
  have fromEndpoint := actual_lambda_child_head sourceMatches source role sourceParent sourceWord
    (.inr (.inr ())) (.inl ()) (.inr true) HEq.rfl sourceFinish
  have sourceHead := source.start
  rw [fromEndpoint] at sourceHead
  obtain ⟨oldTail,sourcePiece⟩ := List.head?_eq_some_iff.mp sourceHead
  obtain ⟨fullTail,writerMiddle,targetPiece,writer,suffix⟩ := unary_copied_lambda_body_fragment cut .bra
    (Bij.refl Unit) (Or.inr rfl) i (j+1) (current:=current) targetMatches target role targetParent targetWord parentFinish pieceLabels
  change List (PlugSegment cut rhs) at fullTail
  change target.segments.map (plugEnd (cut).label (rhs).label).invFun=
    .inr (.inl ⟨.inl (),.inr true⟩)::.inr (.inl ⟨.inr true,.inl ()⟩)::
      .inl (.inr (.inl (.inr (.inr true))))::fullTail at targetPiece
  obtain ⟨pending,whole,oldLabels,_oldEnd,trimmed⟩ := site.bra_aux_canonical_access
    flow root positive sourceMatches principal source.access target.access (source.word.trans target.word.symm)
    false endAt wholeLabels
  have untrimmed : (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
      [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
        .inl (.inr (.inl (.inr (.inr true))))])++fullTail=pending.pre++
          [.inr (.inr (.inl (.inr false))),.inr (.inl ⟨.inr false,.inr ()⟩)] := by
    rw [←trimmed,targetCut.2,List.map_append,targetPiece]
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  obtain ⟨tail,trimmedSplit,tailEq⟩ := trim_after_literal_pivot
    (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
      [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩)])
    fullTail pending.pre (.inl (.inr (.inl (.inr (.inr true)))))
    (.inr (.inr (.inl (.inr false)))) (.inr (.inl ⟨.inr false,.inr ()⟩))
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using untrimmed)
    (by intro h;cases h) (by intro h;cases h)
  have sourceCut := source.child_prefix sourceMatches role sourceParent sourceWord
  have oldSplit : source.access.val=(sourceParent.val++[.inl ⟨.inr (.inr ()),.inr true⟩])++oldTail := by
    rw [sourceCut.2,sourcePiece]
    simp only [List.append_assoc,List.singleton_append]
  have rawSplit : pending.pre=
      (targetParent.val.map (plugEnd (cut).label (rhs).label).invFun++
        [.inr (.inl ⟨.inl (),.inr true⟩),.inr (.inl ⟨.inr true,.inl ()⟩),
          .inl (.inr (.inl (.inr (.inr true))))])++tail := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using trimmedSplit
  have parentLast : (sourceParent.val++[.inl ⟨.inr (.inr ()),.inr true⟩] : List (Endpoint site.net)).getLast?=
      some (site.outsideEnd (.inr (.inl (.inr (.inr true))))) := by
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
    rfl
  obtain ⟨seam,relation,actualLabels⟩ := whole.unary_cut_at_actual_prefix site (by intro h;cases h)
    parentRelation pending.prefixPath.labelling paddedLabels oldSplit rawSplit
    (.inr (.inl (.inr (.inr true)))) parentLast
  refine ⟨tail,oldTail,seam,pending.middle,sourcePiece,?_,?_,actualLabels⟩
  · simpa only [tailEq] using targetPiece
  · simpa only [sourcePiece] using relation
end
end Lamping.AG