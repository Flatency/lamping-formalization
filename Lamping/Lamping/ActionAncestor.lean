import Lamping.Lamping.ActionLocalAncestors
import Lamping.Lamping.SourcePathSiteLift
import Lamping.Lamping.PlugExcursionLifting
import Lamping.Lamping.FlowRootPaths
namespace Lamping.AG
open Graph

inductive IsAction : Schema → Prop
  | fan (f : Op) (i j : Nat) (lt : i<j) : IsAction (.fanAction f i j lt)
  | cro (f : Op) (i j : Nat) (lt : i<j) : IsAction (.croAction f i j lt)
  | bra (f : Op) (i j : Nat) (lt : i<j) : IsAction (.braAction f i j lt)

section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))

theorem PathSite.action_local_route (action : IsAction s) (entry exit : s.Frontier) (a b : Context)
    (path : LocalPath s.right.net entry exit a b) :
    ∃ es : List (Endpoint site.net),
      es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr entry))))) ∧
      es.getLast?=some (site.outsideEnd (.inr (.inl (.inr exit)))) ∧Labelling site.net es a b := by
  cases action with
  | fan f i j lt =>
    obtain ⟨old⟩ := fanAction_local_ancestor f i j lt entry exit a b path
    exact site.left_local_path_lift (Or.inl rfl) entry exit a b old
  | cro f i j lt =>
    obtain ⟨old⟩ := croAction_local_ancestor f i j lt entry exit a b path
    exact site.left_local_path_lift (Or.inr (Or.inl rfl)) entry exit a b old
  | bra f i j lt =>
    obtain ⟨old⟩ := braAction_local_ancestor f i j lt entry exit a b path
    exact site.left_local_path_lift (Or.inr (Or.inr rfl)) entry exit a b old

def ActionResidual (es : List (Endpoint site.reduce)) (old : List (Endpoint site.net)) : Prop :=
  LocalBlockResidual (cutFragment site.net (pathPartition s V) site.closed) s.right.net
    site.net site.outsideEnd (es.map (plugEnd _ _).invFun) old

/-- Actual whole action-step ancestor with the supplied A/B and literal
finite block residual. No local transport oracle is an input. -/
theorem PathSite.action_ancestor (action : IsAction s)
    {es : List (Endpoint site.reduce)} {a b : Context} (labels : Labelling site.reduce es a b)
    (first last : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (head : es.head?=some (AG.plugLeft _ s.right.net first))
    (finish : es.getLast?=some (AG.plugLeft _ s.right.net last)) :
    ∃ old,ActionResidual site es old ∧Labelling site.net old a b ∧
      old.head?=some (site.outsideEnd first) ∧old.getLast?=some (site.outsideEnd last) := by
  have raw := labels.local_excursions _ _ first last head finish
  exact raw.lift_routes _ _ site.net site.outsideEnd site.outsideEnd_wire
    (fun turn => turn.outsideEnd site) (fun entry exit a b path => site.action_local_route action entry exit a b path)
    first last (by rw [List.head?_map,head]; exact congrArg some ((plugEnd _ _).left_inv (.inl first)))
      (by rw [List.getLast?_map,finish]; exact congrArg some ((plugEnd _ _).left_inv (.inl last)))

theorem PathSite.action_root_ancestor (action : IsAction s)
    {boundary : B → Bool} (flow : FlowBalance site.net boundary)
    (root : B) (rootPolarity : boundary root=true)
    {es : List (Endpoint site.reduce)} {a b : Context}
    (labels : Labelling site.reduce es a b) (rooted : es.head?=some (.inr (.inl root)))
    (last : Endpoint (cutFragment site.net (pathPartition s V) site.closed))
    (finish : es.getLast?=some (AG.plugLeft _ s.right.net last)) :
    ∃ old,ActionResidual site es old ∧Labelling site.net old a b ∧Forward site.net old ∧
      old.head?=some (.inr (.inl root)) ∧old.getLast?=some (site.outsideEnd last) := by
  let first : Endpoint (cutFragment site.net (pathPartition s V) site.closed) := .inr (.inl (.inl root))
  have head : es.head?=some (AG.plugLeft _ s.right.net first) := rooted
  obtain ⟨old,residual,oldLabels,oldHead,oldLast⟩ := site.action_ancestor action labels first last head finish
  have oldRoot : old.head?=some (.inr (.inl root)) := oldHead
  exact ⟨old,residual,oldLabels,oldLabels.root_forward_of_flow flow root oldRoot rootPolarity,oldRoot,oldLast⟩
end
end Lamping.AG
