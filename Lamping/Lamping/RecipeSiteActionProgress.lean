import Lamping.Lamping.InternalOccursControlProgress
import Lamping.Lamping.RootedControlActionProgress
import Lamping.Lamping.ExecutableNetTransport
import Lamping.Lamping.NetIsoBetaFiberTransport
import Lamping.Lamping.NetIsoInvariantTransport
import Lamping.Lamping.RootPathInputs
import Lamping.Lamping.GraphIndexedBalance
import Lamping.Lamping.GraphFlowPreservation

namespace Lamping.AG
open Graph Lambda ExposureScheduling
section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature} (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem keptOfProperLabel (node : K ⊕ (Unit ⊕ Unit)) (op : Op) (index : Nat)
    (tag : site.net.label node=label op index)
    (notActive : s.active≠op) (notPassive : s.passive≠op) :
    ∃ k, node=.inl k := by
  rcases node with k | (a | p)
  · exact ⟨k,rfl⟩
  · cases a
    exact False.elim (notActive (Kind.op.inj (congrArg Graph.Label.sort tag)))
  · cases p
    exact False.elim (notPassive (Kind.op.inj (congrArg Graph.Label.sort tag)))

/-- At a control/control site the APP departure and λ arrival belong to the
outside carrier of this very site. -/
theorem RedexConnection.controlSiteOutsideEnds (connection : RedexConnection site.net)
    (activeControl : s.active=.fan ∨ s.active=.cro ∨ s.active=.bra)
    (passiveControl : s.passive=.fan ∨ s.passive=.cro ∨ s.passive=.bra) :
    ∃ first last : Endpoint cut,
      connection.edges.head?=some (site.outsideEnd first) ∧
      connection.edges.getLast?=some (site.outsideEnd last) := by
  rcases connection with ⟨app,lam,appPort,lamPort,appIndex,lamIndex,appLabel,lamLabel,
    appPrincipal,lamPrincipal,es,proper,start,finish,emptyWord⟩
  obtain ⟨appNode,appEq⟩ := keptOfProperLabel site app .app appIndex appLabel
    (by rcases activeControl with h|h|h <;> simp [h])
    (by rcases passiveControl with h|h|h <;> simp [h])
  obtain ⟨lamNode,lamEq⟩ := keptOfProperLabel site lam .lam lamIndex lamLabel
    (by rcases activeControl with h|h|h <;> simp [h])
    (by rcases passiveControl with h|h|h <;> simp [h])
  subst app
  subst lam
  let first : Endpoint cut := .inl ⟨appNode,appPort⟩
  let lamEnd : Endpoint cut := .inl ⟨lamNode,lamPort⟩
  exact ⟨first,(cut).wire lamEnd,start,
    finish.trans (congrArg some (site.outsideEnd_wire lamEnd))⟩
end

namespace Readback
section
variable {B : Type} [FiniteNames B] {s : Schema} {source : ExecutableNet B}
variable {root : B} {current : Lambda.Labelled.LTerm} {redex : RedexOcc current.erase}

/-- Transport the same occurrence, with its literal ordered connection, into
the actual recipe site. -/
theorem ExplicitRewriteRecipe.mappedRedexAccess_edges (recipe : ExplicitRewriteRecipe source s)
    (access : ActualRedexAccess source.graph.net root redex) :
    (recipe.sourceIso.actualRedexAccess access).connection.edges =
      access.connection.edges.map recipe.sourceIso.ends := rfl

/-- An internal action decreases inversions at the actual executable target.
The old word here is measured in the actual recipe site coordinates. -/
theorem ExplicitRewriteRecipe.internalActionProgress (recipe : ExplicitRewriteRecipe source s)
    (action : IsAction s)
    (activeControl : s.active=.fan ∨ s.active=.cro ∨ s.active=.bra)
    (passiveControl : s.passive=.fan ∨ s.passive=.cro ∨ s.passive=.bra)
    (access : ActualRedexAccess source.graph.net root redex)
    (matching : Matches source.graph.net root current.erase)
    (inputs : RootInputs source.graph.net root)
    {directions : B → Bool} {depths : B → Int}
    (flow : Nonempty (FlowBalance source.graph.net directions)) (positive : directions root=true)
    (balance : Nonempty (IndexedLevelBalance source.graph.net depths)) (rootDepth : depths root=0)
    (oldT : Transparency source.graph.net root)
    (principal : SiteActionPrincipal recipe.site)
    (internal : Bool ⊕ (recipe.InternalWire × Bool))
    (selected : recipe.site.internalEnd internal ∈ access.connection.edges.map recipe.sourceIso.ends) :
    ∃ target : ActualRedexAccess recipe.target.graph.net root redex,
      (controlWord recipe.target.graph.net target.connection.edges).length =
        (controlWord recipe.site.net (recipe.sourceIso.actualRedexAccess access).connection.edges).length ∧
      inversions (controlWord recipe.target.graph.net target.connection.edges) <
        inversions (controlWord recipe.site.net (recipe.sourceIso.actualRedexAccess access).connection.edges) := by
  let iso := recipe.sourceIso
  let mapped := iso.actualRedexAccess access
  obtain ⟨flow⟩ := flow
  obtain ⟨balance⟩ := balance
  obtain ⟨a,b,labels⟩ := access.child.property.1.1
  obtain ⟨first,last,head,finish⟩ :=
    mapped.connection.controlSiteOutsideEnds recipe.site activeControl passiveControl
  obtain ⟨target,_child,_seam,_old,_new,_canonical,length,strict⟩ :=
    mapped.internal_action_word_progress_of_internal_occurs recipe.site action passiveControl
      (iso.labelling labels) (iso.matches matching) (iso.rootInputs inputs)
      (iso.flowBalance flow) positive (iso.indexed_balance balance) rootDepth
      (iso.transparency oldT) principal first last head finish internal selected
  exact ⟨target,length,strict⟩
end
end Readback
end Lamping.AG
