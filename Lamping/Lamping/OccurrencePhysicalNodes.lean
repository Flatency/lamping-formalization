import Lamping.Lamping.ChainFragmentUniqueness
import Lamping.Lambda.SyntaxIncidence

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]

/-- A fixed current proper occurrence has an actual rooted access and physical context node. No injectivity between different occurrences is asserted. -/
structure PhysicalContextOccurrence (current : LTerm) (g : Net signature N B W)
    (root : B) (position : Path) where
  access : RootAccess g root
  word : accessWord g access.val=position
  node : N
  port : Port (g.label node).sort
  context : ((g.label node).sort=.op .app ∧ HEq port appCtx) ∨
    ((g.label node).sort=.op .lam ∧ HEq port (Sum.inl () : Port (.op .lam)))
  finish : access.val.getLast?=some (g.wire (.inl ⟨node,port⟩))

/-- Actual Matches supplies the context endpoint, including for repeated current labels. -/
theorem Matches.physical_context_occurrence
    {current : LTerm} {g : Net signature N B W} {root : B}
    (matching : Matches g root current.erase) (closed : Closed current.erase)
    (proper : SyntaxIncidence.ProperAt current position) :
    Nonempty (PhysicalContextOccurrence current g root position) := by
  rcases proper with ⟨stamp,fn,arg,lookup⟩ | ⟨stamp,body,lookup⟩
  · let atPosition : Position current.erase := ⟨position,by
      rw [←LTerm.erase_subterm,lookup]; rfl⟩
    obtain ⟨access,word,_⟩ := Matches.observation g matching atPosition
    obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup current lookup [] .external
    obtain ⟨terminal,realizes,finish⟩ := matching.source_edge_terminal closed occurrence access word
    change SourcePortRealizes current g root (.appContext stamp) terminal at realizes
    cases realizes with
    | departure _ role => cases role
    | appContext _ _ _ shape role _ =>
      exact ⟨⟨access,word,_,_,Or.inl ⟨shape,role⟩,finish⟩⟩
  · let atPosition : Position current.erase := ⟨position,by
      rw [←LTerm.erase_subterm,lookup]; rfl⟩
    obtain ⟨access,word,_⟩ := Matches.observation g matching atPosition
    obtain ⟨env,ctx,occurrence⟩ := SourceSubterm.of_lookup current lookup [] .external
    obtain ⟨terminal,realizes,finish⟩ := matching.source_edge_terminal closed occurrence access word
    change SourcePortRealizes current g root (.lamContext stamp) terminal at realizes
    cases realizes with
    | departure _ role => cases role
    | lamContext _ _ _ shape role _ =>
      exact ⟨⟨access,word,_,_,Or.inr ⟨shape,role⟩,finish⟩⟩

/-- Word injectivity and the actual same context endpoint identify the node at one literal occurrence. -/
theorem PhysicalContextOccurrence.node_unique
    {current : LTerm} {g : Net signature N B W} {root : B}
    (matching : Matches g root current.erase)
    (first second : PhysicalContextOccurrence current g root position) : first.node=second.node := by
  have accesses : first.access=second.access :=
    matching.accessWord_injective (first.word.trans second.word.symm)
  have sameLast := congrArg (fun access : RootAccess g root => access.val.getLast?) accesses
  have lasts := first.finish.symm.trans (sameLast.trans second.finish)
  have wires := Option.some.inj lasts
  have endpoints := congrArg g.wire wires
  simp only [Pairing.involutive] at endpoints
  exact congrArg Sigma.fst (Sum.inl.inj endpoints)

abbrev PhysicalContextSelection (current : LTerm) (g : Net signature N B W) (root : B) :=
  (position : SyntaxIncidence.ProperPosition current) →
    PhysicalContextOccurrence current g root position.val

 theorem Matches.physical_context_selection
    {current : LTerm} {g : Net signature N B W} {root : B}
    (matching : Matches g root current.erase) (closed : Closed current.erase) :
    Nonempty (PhysicalContextSelection current g root) := by
  classical
  exact ⟨fun position=>Classical.choice (matching.physical_context_occurrence closed position.property)⟩

end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

def physicalSyntaxVertex (selection : PhysicalContextSelection current g root) :
    SyntaxIncidence.Vertex current → B ⊕ N
  | none => .inl root
  | some position => .inr (selection position).node

def endpointVertex : Endpoint g → Option (B ⊕ N)
  | .inl port => some (.inr port.fst)
  | .inr (.inl boundary) => some (.inl boundary)
  | .inr (.inr _) => none

private theorem fragment_access_finish (fragment : SourceEdgeFragment current g root edge position) :
    fragment.access.val.getLast?=some (g.wire fragment.toEndpoint) := by
  rw [fragment.literal,List.getLast?_append,fragment.finish]; rfl
/-- The target is the same occurrence for compound terms and the actual lexical binder for variables. This is endpoint incidence, not an ordinary binder-to-context turn. -/
theorem OccurrenceFragment.target_vertex
    (matching : Matches g root current.erase) (closed : Closed current.erase)
    (selection : PhysicalContextSelection current g root)
    (edge : SyntaxIncidence.Edge current) (fragment : OccurrenceFragment current g root edge.val) :
    endpointVertex fragment.fragment.toEndpoint=
      some (physicalSyntaxVertex selection (SyntaxIncidence.target current closed edge)) := by
  rcases fragment with ⟨sub,env,ctx,occurrence,fragment⟩
  cases sub with
  | app stamp fn arg =>
    let vertex : SyntaxIncidence.ProperPosition current :=
      ⟨edge.val,Or.inl ⟨stamp,fn,arg,occurrence.lookup⟩⟩
    have atTarget := SyntaxIncidence.target_eq_of_spec current closed edge
      (vertex:=some vertex) (Or.inl rfl)
    rw [atTarget]
    have realizes := fragment.toRealizes
    change SourcePortRealizes current g root (.appContext stamp) fragment.toEndpoint at realizes
    generalize endpointEq : fragment.toEndpoint=endpoint at realizes
    cases realizes with
    | departure _ role => cases role
    | appContext _ _ _ shape role _ =>
      have finish := fragment_access_finish fragment
      rw [endpointEq] at finish
      let physical : PhysicalContextOccurrence current g root vertex.val :=
        ⟨fragment.access,fragment.word,_,_,Or.inl ⟨shape,role⟩,finish⟩
      have nodes := PhysicalContextOccurrence.node_unique matching (selection vertex) physical
      change some (Sum.inr physical.node)=some (Sum.inr (selection vertex).node)
      rw [nodes]
  | lam stamp body =>
    let vertex : SyntaxIncidence.ProperPosition current :=
      ⟨edge.val,Or.inr ⟨stamp,body,occurrence.lookup⟩⟩
    have atTarget := SyntaxIncidence.target_eq_of_spec current closed edge
      (vertex:=some vertex) (Or.inl rfl)
    rw [atTarget]
    have realizes := fragment.toRealizes
    change SourcePortRealizes current g root (.lamContext stamp) fragment.toEndpoint at realizes
    generalize endpointEq : fragment.toEndpoint=endpoint at realizes
    cases realizes with
    | departure _ role => cases role
    | lamContext _ _ _ shape role _ =>
      have finish := fragment_access_finish fragment
      rw [endpointEq] at finish
      let physical : PhysicalContextOccurrence current g root vertex.val :=
        ⟨fragment.access,fragment.word,_,_,Or.inr ⟨shape,role⟩,finish⟩
      have nodes := PhysicalContextOccurrence.node_unique matching (selection vertex) physical
      change some (Sum.inr physical.node)=some (Sum.inr (selection vertex).node)
      rw [nodes]
  | var stamp index =>
    have variableLookup : subtermAt current.erase edge.val=some (.var index) := by
      rw [←LTerm.erase_subterm,occurrence.lookup]; rfl
    have scope := scoped_subterm closed variableLookup
    have inEnv : index<env.length := by
      rw [occurrence.env_length]
      exact scope
    let origin := env[index]
    have entry : env[index]?=some origin := List.getElem?_eq_getElem inEnv
    have bound : sourceBinder env index=.lamBind origin := by simp only [sourceBinder,entry]
    obtain ⟨parent,loop,a,b,c,binding,actualCtx,body,split,contextRole,parentFinish,
      _labels,atBinder,words,depth⟩ :=
      matching.original_source_binder occurrence bound fragment.access fragment.word
    let vertex : SyntaxIncidence.ProperPosition current :=
      ⟨accessWord g parent.val,Or.inr ⟨origin,body,atBinder⟩⟩
    have atTarget := SyntaxIncidence.target_eq_of_spec current closed edge (vertex:=some vertex)
      (Or.inr ⟨stamp,index,origin,body,accessWord g loop,occurrence.lookup,atBinder,words,depth⟩)
    let physical : PhysicalContextOccurrence current g root vertex.val :=
      ⟨parent,rfl,binding.binder,actualCtx,Or.inr ⟨binding.isLam,contextRole⟩,parentFinish⟩
    have nodes := PhysicalContextOccurrence.node_unique matching (selection vertex) physical
    have last : fragment.access.val.getLast?=some (g.wire (.inl ⟨binding.binder,binding.bind⟩)) := by
      rw [split,List.getLast?_append,binding.finish]; rfl
    have wires := Option.some.inj ((fragment_access_finish fragment).symm.trans last)
    have endpoints := congrArg g.wire wires
    simp only [Pairing.involutive] at endpoints
    rw [atTarget,endpoints]
    change some (Sum.inr physical.node)=some (Sum.inr (selection vertex).node)
    rw [nodes]

end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

private theorem child_context_role {kind : Kind} {ctx out : Port kind}
    (roles : SyntaxChildPorts kind ctx out step) :
    (kind=.op .app ∧HEq ctx appCtx) ∨
    (kind=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam))) := by
  cases roles
  all_goals first | exact Or.inl ⟨rfl,HEq.rfl⟩ | exact Or.inr ⟨rfl,HEq.rfl⟩

/-- The physical departure lies on the actual parent occurrence, determined by the last syntax token and its literal prefix. -/
theorem OccurrenceFragment.source_vertex
    (matching : Matches g root current.erase)
    (selection : PhysicalContextSelection current g root)
    (edge : SyntaxIncidence.Edge current) (fragment : OccurrenceFragment current g root edge.val) :
    endpointVertex fragment.fragment.fromEndpoint=
      some (physicalSyntaxVertex selection (SyntaxIncidence.source current edge)) := by
  rcases fragment with ⟨sub,env,ctx,occurrence,fragment⟩
  rcases occurrence.last_departure with ⟨empty,external⟩ |
    ⟨parentPath,step,parentTerm,split,lookup,role⟩
  · have atSource := SyntaxIncidence.source_eq_of_spec current edge (vertex:=none) empty
    rw [atSource]
    have sourceFrom : (sourceEdge env ctx sub).fromPort=.external := by cases sub <;> exact external
    have realizes := fragment.fromRealizes
    rw [sourceFrom] at realizes
    generalize endpointEq : fragment.fromEndpoint=endpoint at realizes
    cases realizes with
    | external => rfl
    | departure _ role => cases role
  · have proper : SyntaxIncidence.ProperAt current parentPath := by
      cases role with
      | fn => exact Or.inl ⟨_,_,_,lookup⟩
      | arg => exact Or.inl ⟨_,_,_,lookup⟩
      | body => exact Or.inr ⟨_,_,lookup⟩
    let vertex : SyntaxIncidence.ProperPosition current := ⟨parentPath,proper⟩
    have atSource := SyntaxIncidence.source_eq_of_spec current edge (vertex:=some vertex)
      ⟨step,parentTerm,ctx,split,lookup,role⟩
    rw [atSource]
    let parentPosition : Position current.erase := ⟨parentPath,by
      rw [←LTerm.erase_subterm,lookup]; rfl⟩
    obtain ⟨parent,parentWord,_⟩ := Matches.observation g matching parentPosition
    have childWord : accessWord g fragment.access.val=accessWord g parent.val++[step] := by
      rw [fragment.word,parentWord]; exact split
    obtain ⟨node,physicalCtx,departure,tail,roles,parentFinish,childSplit,_forward,_assignments⟩ :=
      matching.syntax_child_fragment parent fragment.access step childWord
    let physical : PhysicalContextOccurrence current g root vertex.val :=
      ⟨parent,parentWord,node,physicalCtx,child_context_role roles,parentFinish⟩
    have nodes := PhysicalContextOccurrence.node_unique matching (selection vertex) physical
    have sourceFrom : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
    have actualRole : SourceDeparture parentTerm step (sourceEdge env ctx sub).fromPort := by
      rw [sourceFrom]; exact role
    have word : edge.val=accessWord g parent.val++[step] := by rw [parentWord]; exact split
    have cut := fragment.child_prefix matching actualRole parent word
    have segments : fragment.segments=(.inl ⟨node,departure⟩)::tail :=
      List.append_cancel_left (cut.2.symm.trans childSplit)
    have first := fragment.start
    rw [segments,List.head?_cons] at first
    have endpointEq := Option.some.inj first
    rw [←endpointEq]
    change some (Sum.inr physical.node)=some (Sum.inr (selection vertex).node)
    rw [nodes]

end
end Lamping.AG
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

theorem physicalSyntaxVertex_choice_independent (matching : Matches g root current.erase)
    (first second : PhysicalContextSelection current g root) :
    physicalSyntaxVertex first=physicalSyntaxVertex second := by
  funext vertex
  cases vertex with
  | none => rfl
  | some position =>
    change Sum.inr (first position).node=Sum.inr (second position).node
    exact congrArg Sum.inr (PhysicalContextOccurrence.node_unique matching _ _)

theorem OccurrenceFragment.incidence_vertices
    (matching : Matches g root current.erase) (closed : Closed current.erase)
    (selection : PhysicalContextSelection current g root)
    (edge : SyntaxIncidence.Edge current) (fragment : OccurrenceFragment current g root edge.val) :
    endpointVertex fragment.fragment.fromEndpoint=
      some (physicalSyntaxVertex selection (SyntaxIncidence.source current edge)) ∧
    endpointVertex fragment.fragment.toEndpoint=
      some (physicalSyntaxVertex selection (SyntaxIncidence.target current closed edge)) :=
  ⟨fragment.source_vertex matching selection edge,fragment.target_vertex matching closed selection edge⟩

/-- An actual occurrence-indexed fragmented incidence realization follows
from Matches. It contains no chain isomorphism or REP conclusion. -/
theorem Matches.occurrence_incidence_realization
    (matching : Matches g root current.erase) (closed : Closed current.erase) :
    ∃ fragments : OccurrenceFragmentSelection current g root,
    ∃ nodes : PhysicalContextSelection current g root,
    ∀ edge : SyntaxIncidence.Edge current,
      endpointVertex (fragments edge).fragment.fromEndpoint=
        some (physicalSyntaxVertex nodes (SyntaxIncidence.source current edge)) ∧
      endpointVertex (fragments edge).fragment.toEndpoint=
        some (physicalSyntaxVertex nodes (SyntaxIncidence.target current closed edge)) := by
  obtain ⟨fragments⟩ := matching.occurrence_fragment_selection closed
  obtain ⟨nodes⟩ := matching.physical_context_selection closed
  exact ⟨fragments,nodes,fun edge=>(fragments edge).incidence_vertices matching closed nodes edge⟩

end
end Lamping.AG