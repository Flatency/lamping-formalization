import Lamping.Lamping.ActionFragmentCuts
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

theorem PathSite.action_kept_canonical_access (action : IsAction s)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {term : Term}
    (matching : Matches site.net root term) (principal : SiteActionPrincipal site)
    (source : RootAccess site.net root) (target : RootAccess site.reduce root)
    (word : accessWord site.net source.val=accessWord site.reduce target.val)
    (node : K) (p : Port (kept node).sort)
    (finish : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,p⟩)))
    {a b : Context} (labels : Labelling site.reduce target.val a b) :
    ActionCanonicalBlocks site principal (target.val.map (plugEnd (cut).label s.right.net.label).invFun)
      source.val ∧Labelling site.net source.val a b ∧
      source.val.getLast?=some (site.net.wire (.inl ⟨.inl node,p⟩)) := by
  let first : Endpoint cut := .inr (.inl (.inl root))
  let last : Endpoint cut := (cut).wire (.inl ⟨node,p⟩)
  have lastImage : AG.plugLeft cut s.right.net last=site.reduce.wire (.inl ⟨.inl node,p⟩) :=
    (plugLeft_wire cut s.right.net (.inl ⟨node,p⟩)).symm
  have starts : target.val.head?=some (AG.plugLeft cut s.right.net first) := target.property.2.1
  have ends : target.val.getLast?=some (AG.plugLeft cut s.right.net last) := finish.trans (congrArg some lastImage.symm)
  have path := labels.local_excursions cut s.right.net first last starts ends
  have rawHead : (target.val.map (plugEnd (cut).label s.right.net.label).invFun).head?=some (.inl first) := by
    rw [List.head?_map,starts]
    exact congrArg some ((plugEnd (cut).label s.right.net.label).left_inv (.inl first))
  have rawLast : (target.val.map (plugEnd (cut).label s.right.net.label).invFun).getLast?=some (.inl last) := by
    rw [List.getLast?_map,ends]
    exact congrArg some ((plugEnd (cut).label s.right.net.label).left_inv (.inl last))
  obtain ⟨old,relation,oldLabels,oldHead,oldLast⟩ :=
    path.action_canonical_lift site action principal first last rawHead rawLast
  have words := relation.word site path
  rw [plug_decomposition_flatten] at words
  have rooted : old.head?=some (.inr (.inl root)) := oldHead
  have oldEnd : old.getLast?=some (site.net.wire (.inl ⟨.inl node,p⟩)) := by
    change old.getLast?=some (site.outsideEnd ((cut).wire (.inl ⟨node,p⟩))) at oldLast
    rw [←site.outsideEnd_wire] at oldLast
    exact oldLast
  have kind : accessKind site.net old=accessKind site.reduce target.val := by
    simp only [accessKind,oldEnd,finish,Option.bind_some,Pairing.involutive]
    rfl
  have typed : ∃ k,accessKind site.net old=some k := by rw [kind];exact target.property.2.2
  have forward := oldLabels.root_forward_of_flow flow root rooted positive
  let oldAccess : RootAccess site.net root := ⟨old,⟨⟨⟨a,b,oldLabels⟩,forward⟩,rooted,typed⟩⟩
  have same : oldAccess=source := matching.accessWord_injective (words.symm.trans word.symm)
  have literal : old=source.val := congrArg Subtype.val same
  rw [literal] at relation oldLabels oldEnd
  exact ⟨relation,oldLabels,oldEnd⟩

theorem SourceEdgeFragment.unary_kept_parent_cut (action : IsAction s) (unary : s.active≠.fan)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase)
    (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {edge : SourceEdge} {position : Path}
    (source : SourceEdgeFragment current site.net root edge position)
    (target : SourceEdgeFragment current site.reduce root edge position)
    {parentTerm : LTerm} {step : Step} (role : SourceDeparture parentTerm step edge.fromPort)
    (sourceParent : RootAccess site.net root) (targetParent : RootAccess site.reduce root)
    (sourceWord : position=accessWord site.net sourceParent.val++[step])
    (targetWord : position=accessWord site.reduce targetParent.val++[step])
    (parentNode endNode : K) (parentPort : Port (kept parentNode).sort) (endPort : Port (kept endNode).sort)
    (parentEnd : targetParent.val.getLast?=some (site.reduce.wire (.inl ⟨.inl parentNode,parentPort⟩)))
    (endAt : target.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl endNode,endPort⟩)))
    {a b : Context} (labels : Labelling site.reduce target.access.val a b) :
    ∃ pivot : Endpoint cut,∃ seam : Context,
      sourceParent.val.getLast?=some (site.outsideEnd pivot) ∧
      targetParent.val.getLast?=some (AG.plugLeft cut s.right.net pivot) ∧
      ActionCanonicalBlocks site principal
        (Sum.inl pivot::target.segments.map (plugEnd (cut).label s.right.net.label).invFun)
        (site.outsideEnd pivot::source.segments) ∧
      PlugLabelling cut s.right.net
        (Sum.inl pivot::target.segments.map (plugEnd (cut).label s.right.net.label).invFun) seam b := by
  obtain ⟨whole,_sourceLabels,_sourceEnd⟩ := site.action_kept_canonical_access action flow root positive
    sourceMatches principal source.access target.access (source.word.trans target.word.symm)
    endNode endPort endAt labels
  obtain ⟨c,d,parentLabels⟩ := targetParent.property.1.1
  have parentWord : accessWord site.net sourceParent.val=accessWord site.reduce targetParent.val :=
    List.append_cancel_right (sourceWord.symm.trans targetWord)
  obtain ⟨parent,_parentSourceLabels,parentLast⟩ := site.action_kept_canonical_access action flow root positive
    sourceMatches principal sourceParent targetParent parentWord parentNode parentPort parentEnd parentLabels
  let pivot : Endpoint cut := (cut).wire (.inl ⟨parentNode,parentPort⟩)
  have parentOutside : sourceParent.val.getLast?=some (site.outsideEnd pivot) := by
    change sourceParent.val.getLast?=some (site.outsideEnd ((cut).wire (.inl ⟨parentNode,parentPort⟩)))
    rw [←site.outsideEnd_wire]
    exact parentLast
  have oldSplit := (source.child_prefix sourceMatches role sourceParent sourceWord).2
  have newSplit := (target.child_prefix targetMatches role targetParent targetWord).2
  have rawSplit := congrArg (fun xs=>xs.map (plugEnd (cut).label s.right.net.label).invFun) newSplit
  simp only [List.map_append] at rawSplit
  obtain ⟨seam,relation,pieceLabels⟩ := whole.unary_cut_at_actual_prefix site unary parent
    (labels.plug_decomposition cut s.right.net) (parentLabels.plug_decomposition cut s.right.net)
    oldSplit rawSplit pivot parentOutside
  have targetOutside : targetParent.val.getLast?=some (AG.plugLeft cut s.right.net pivot) :=
    parentEnd.trans (congrArg some (plugLeft_wire cut s.right.net (.inl ⟨parentNode,parentPort⟩)))
  exact ⟨pivot,seam,parentOutside,targetOutside,relation,pieceLabels⟩

private theorem outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  have mapped := congrArg split same
  change split (split.invFun (.inl e))=split (split.invFun (.inl f)) at mapped
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

private theorem plugLeft_injective : Function.Injective (AG.plugLeft cut s.right.net) := by
  intro e f same
  have mapped := congrArg (plugEnd (cut).label s.right.net.label).invFun same
  change (plugEnd (cut).label s.right.net.label).invFun ((plugEnd (cut).label s.right.net.label) (.inl e))=
    (plugEnd (cut).label s.right.net.label).invFun ((plugEnd (cut).label s.right.net.label) (.inl f)) at mapped
  rw [Bij.left_inv,Bij.left_inv] at mapped
  exact Sum.inl.inj mapped

theorem SourceEdgeFragment.unary_kept_piece_equality (action : IsAction s) (unary : s.active≠.fan)
    {directions : B → Bool} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true) {current : LTerm}
    (sourceMatches : Matches site.net root current.erase) (targetMatches : Matches site.reduce root current.erase)
    (principal : SiteActionPrincipal site) {firstEdge secondEdge : SourceEdge} {p q : Path}
    (sourceFirst : SourceEdgeFragment current site.net root firstEdge p)
    (targetFirst : SourceEdgeFragment current site.reduce root firstEdge p)
    (sourceSecond : SourceEdgeFragment current site.net root secondEdge q)
    (targetSecond : SourceEdgeFragment current site.reduce root secondEdge q)
    {leftTerm rightTerm : LTerm} {leftStep rightStep : Step}
    (leftRole : SourceDeparture leftTerm leftStep firstEdge.fromPort)
    (rightRole : SourceDeparture rightTerm rightStep secondEdge.fromPort)
    (sourceLeft sourceRight : RootAccess site.net root) (targetLeft targetRight : RootAccess site.reduce root)
    (sourceLeftWord : p=accessWord site.net sourceLeft.val++[leftStep])
    (sourceRightWord : q=accessWord site.net sourceRight.val++[rightStep])
    (targetLeftWord : p=accessWord site.reduce targetLeft.val++[leftStep])
    (targetRightWord : q=accessWord site.reduce targetRight.val++[rightStep])
    (leftParent rightParent leftEnd rightEnd : NodePort signature K kept)
    (leftParentAt : targetLeft.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftParent.1,leftParent.2⟩)))
    (rightParentAt : targetRight.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightParent.1,rightParent.2⟩)))
    (leftEndAt : targetFirst.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl leftEnd.1,leftEnd.2⟩)))
    (rightEndAt : targetSecond.access.val.getLast?=some (site.reduce.wire (.inl ⟨.inl rightEnd.1,rightEnd.2⟩))) :
    targetFirst.segments=targetSecond.segments ↔sourceFirst.segments=sourceSecond.segments := by
  obtain ⟨a,b,leftLabels⟩ := targetFirst.access.property.1.1
  obtain ⟨c,d,rightLabels⟩ := targetSecond.access.property.1.1
  obtain ⟨lp,ls,leftOldLast,leftNewLast,leftRelation,leftPieceLabels⟩ :=
    sourceFirst.unary_kept_parent_cut site action unary flow root positive sourceMatches targetMatches principal
      targetFirst leftRole sourceLeft targetLeft sourceLeftWord targetLeftWord leftParent.1 leftEnd.1
      leftParent.2 leftEnd.2 leftParentAt leftEndAt leftLabels
  obtain ⟨rp,rs,rightOldLast,rightNewLast,rightRelation,rightPieceLabels⟩ :=
    sourceSecond.unary_kept_parent_cut site action unary flow root positive sourceMatches targetMatches principal
      targetSecond rightRole sourceRight targetRight sourceRightWord targetRightWord rightParent.1 rightEnd.1
      rightParent.2 rightEnd.2 rightParentAt rightEndAt rightLabels
  constructor
  · intro pieces
    have parentSame := SourceEdgeFragment.equal_piece_parent_seams targetMatches targetFirst targetSecond
      leftRole rightRole targetLeft targetRight targetLeftWord targetRightWord pieces
    have mappedSame := Option.some.inj (leftNewLast.symm.trans (parentSame.trans rightNewLast))
    have pivots := plugLeft_injective site mappedSame
    subst rp
    rw [pieces] at leftRelation
    exact (List.cons.inj (leftRelation.fixed_source_unique site rightRelation)).2
  · intro pieces
    have parentSame := SourceEdgeFragment.equal_piece_parent_seams sourceMatches sourceFirst sourceSecond
      leftRole rightRole sourceLeft sourceRight sourceLeftWord sourceRightWord pieces
    have outsideSame := Option.some.inj (leftOldLast.symm.trans (parentSame.trans rightOldLast))
    have pivots := outside_injective site outsideSame
    subst rp
    have rawSame := leftRelation.unary_target_unique_of_labels site unary rightRelation
      leftPieceLabels rightPieceLabels (by rw [pieces])
    have maps := (List.cons.inj rawSame).2
    have physical := congrArg (fun xs=>xs.map (plugEnd (cut).label s.right.net.label)) maps
    simp only [List.map_map,Function.comp_def,Bij.right_inv] at physical
    change targetFirst.segments.map id=targetSecond.segments.map id at physical
    simpa only [List.map_id] using physical
end
end Lamping.AG