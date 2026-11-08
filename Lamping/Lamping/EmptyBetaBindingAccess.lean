import Lamping.Lamping.EmptyBetaAccessForward
import Lamping.Lamping.ExteriorPlugReflection
namespace Lamping.AG
open Graph Lambda
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition (Schema.beta i) V) site.closed
local notation "rhs" => wires Bool Bool boolFlip

private theorem map_option {T U : Type} (f : T → U) (inject : Function.Injective f)
    (value : Option T) (x : T) (same : value.map f=some (f x)) : value=some x := by
  cases value with
  | none => cases same
  | some y => exact congrArg some (inject (Option.some.inj same))

private theorem outside_word {es : List (Endpoint cut)} {a b : Context}
    (labels : Labelling cut es a b) :
    accessWord site.net (es.map site.outsideEnd)=accessWord cut es := by
  induction labels with
  | single e a => rfl
  | @cons e f tail a middle b turn after ih =>
    have word : arrivalWord site.net (site.outsideEnd f)=arrivalWord cut f := by
      rcases f with ⟨node,p⟩ | ((boundary|frontier)|⟨vertex,direction⟩)
      · rfl
      · exact False.elim (turn.reverse.not_boundary (.inl boundary) rfl)
      · exact False.elim (turn.reverse.not_boundary (.inr frontier) rfl)
      · rfl
    change arrivalWord site.net (site.outsideEnd f)++
      (tail.map site.outsideEnd).flatMap (arrivalWord site.net)=
      arrivalWord cut f++tail.flatMap (arrivalWord cut)
    change (tail.map site.outsideEnd).flatMap (arrivalWord site.net)=
      tail.flatMap (arrivalWord cut) at ih
    rw [word,ih]

/-- Reflect the actual chosen target binding occurrence, not an arbitrary
binder of the same kind. Its literal exterior loop preserves the full word
and therefore the index, with the original suffix assignments and shell. -/
theorem PathSite.empty_beta_binding_access_backward
    {root : B} {t : Term} (matching : Matches site.net root t)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root) (empty : site.betaSyntaxFiber root t=[])
    (target : RootAccess site.reduce root) {index : Nat}
    (suffix : BindingSuffix site.reduce target.val index) :
    ∃ source : RootAccess site.net root,
      accessWord site.net source.val=accessWord site.reduce target.val ∧
      accessKind site.net source.val=accessKind site.reduce target.val ∧
      BindingSuffix site.net source.val index := by
  obtain ⟨outside,a,b,physical,labels,head⟩ :=
    site.empty_beta_access_exterior matching flow positive oldT empty target
  obtain ⟨pre,loop,initial,middle,final,binding,ctx,split,ctxRole,preEnd,preLabels,indexEq⟩ := suffix
  rcases binding with ⟨binder,isLam,body,bind,bodyRole,bindRole,loopHead,loopEnd,loopLabels,loopForward,shell⟩
  cases binder with
  | inr node => exact nomatch node
  | inl node =>
    obtain ⟨cutPre,cutLoop,outsideEq,preEq,loopEq⟩ :=
      List.map_eq_append_iff.mp (physical.symm.trans split)
    change cutPre.map (AG.plugLeft cut rhs)=pre at preEq
    change cutLoop.map (AG.plugLeft cut rhs)=loop at loopEq
    have cutPreLabels : Labelling cut cutPre initial middle := by
      apply Labelling.plugLeft_reflect cut rhs
      rw [preEq]; exact preLabels
    have cutLoopLabels : Labelling cut cutLoop middle final := by
      apply Labelling.plugLeft_reflect cut rhs
      rw [loopEq]; exact loopLabels
    have inject : Function.Injective (AG.plugLeft cut rhs) := by
      intro x y same
      exact Sum.inl.inj ((plugEnd (cut).label (rhs).label).injective same)
    have cutPreEnd : cutPre.getLast?=some ((cut).wire (.inl ⟨node,ctx⟩)) := by
      apply map_option (AG.plugLeft cut rhs) inject
      have actual := preEnd
      rw [←preEq,List.getLast?_map] at actual
      exact actual.trans (congrArg some (plugLeft_wire cut rhs (.inl ⟨node,ctx⟩)))
    have cutLoopHead : cutLoop.head?=some (.inl ⟨node,body⟩) := by
      apply map_option (AG.plugLeft cut rhs) inject
      rw [←loopEq,List.head?_map] at loopHead
      exact loopHead
    have cutLoopEnd : cutLoop.getLast?=some ((cut).wire (.inl ⟨node,bind⟩)) := by
      apply map_option (AG.plugLeft cut rhs) inject
      rw [←loopEq,List.getLast?_map] at loopEnd
      exact loopEnd.trans (congrArg some (plugLeft_wire cut rhs (.inl ⟨node,bind⟩)))
    have sourceLabels := labels.outsideEnd site
    have sourceRoot : (outside.map site.outsideEnd).head?=some (.inr (.inl root)) := by
      rw [List.head?_map,head]; rfl
    have sourceForward := sourceLabels.root_forward_of_flow flow root sourceRoot positive
    have sourceLoopHead : (cutLoop.map site.outsideEnd).head?=some (.inl ⟨.inl node,body⟩) := by
      rw [List.head?_map,cutLoopHead]; rfl
    have sourceLoopEnd : (cutLoop.map site.outsideEnd).getLast?=some (site.net.wire (.inl ⟨.inl node,bind⟩)) := by
      rw [List.getLast?_map,cutLoopEnd]
      exact congrArg some (site.outsideEnd_wire (.inl ⟨node,bind⟩)).symm
    have bodyAt : (outside.map site.outsideEnd)[cutPre.length]?=some (.inl ⟨.inl node,body⟩) := by
      rw [outsideEq,List.map_append,List.getElem?_append_right (by simp),List.length_map,Nat.sub_self]
      simpa only [List.head?_eq_getElem?] using sourceLoopHead
    have sourceLoopForward := sourceForward.suffix_at cutPre.length _ bodyAt
    rw [outsideEq,List.map_append,List.drop_append,List.length_map] at sourceLoopForward
    have dropped : (cutPre.map site.outsideEnd).drop cutPre.length=[] := by
      have h : (cutPre.map site.outsideEnd).drop (cutPre.map site.outsideEnd).length=[] := List.drop_length
      simpa only [List.length_map] using h
    simp only [dropped,Nat.sub_self,List.drop_zero,List.nil_append] at sourceLoopForward
    let oldBinding : BindingLoop site.net (cutLoop.map site.outsideEnd) middle final := {
      binder := .inl node, isLam := isLam, body := body, bind := bind,
      body_role := bodyRole, bind_role := bindRole, start := sourceLoopHead,
      finish := sourceLoopEnd, proper := cutLoopLabels.outsideEnd site,
      forward := sourceLoopForward, shell := shell }
    have oldPreEnd : (cutPre.map site.outsideEnd).getLast?=some (site.net.wire (.inl ⟨.inl node,ctx⟩)) := by
      rw [List.getLast?_map,cutPreEnd]
      exact congrArg some (site.outsideEnd_wire (.inl ⟨node,ctx⟩)).symm
    have oldEnd : (outside.map site.outsideEnd).getLast?=some (site.net.wire (.inl ⟨.inl node,bind⟩)) := by
      rw [outsideEq,List.map_append,List.getLast?_append,sourceLoopEnd,Option.some_or]
    have targetEnd : target.val.getLast?=some (site.reduce.wire (.inl ⟨.inl node,bind⟩)) := by
      rw [split,List.getLast?_append,loopEnd,Option.some_or]
    have kind : accessKind site.net (outside.map site.outsideEnd)=accessKind site.reduce target.val := by
      simp only [accessKind,oldEnd,targetEnd,Option.bind_some,Pairing.involutive]; rfl
    have typed : ∃ k,accessKind site.net (outside.map site.outsideEnd)=some k := by
      rw [kind]; exact target.property.2.2
    refine ⟨⟨outside.map site.outsideEnd,⟨⟨⟨a,b,sourceLabels⟩,sourceForward⟩,sourceRoot,typed⟩⟩,?_,kind,?_⟩
    · rw [physical]
      exact (outside_word site labels).trans (accessWord_plugLeft cut rhs outside).symm
    · refine ⟨cutPre.map site.outsideEnd,cutLoop.map site.outsideEnd,initial,middle,final,
        oldBinding,ctx,by simp only [outsideEq,List.map_append],ctxRole,oldPreEnd,cutPreLabels.outsideEnd site,?_⟩
      have word : accessWord site.net (cutLoop.map site.outsideEnd)=accessWord site.reduce loop := by
        rw [←loopEq]
        exact (outside_word site cutLoopLabels).trans (accessWord_plugLeft cut rhs cutLoop).symm
      exact indexEq.trans (congrArg binderDepth word).symm
end
end Lamping.AG


