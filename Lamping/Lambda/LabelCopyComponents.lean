import Lamping.Lambda.LabelFirstCandidateOrder
import Lamping.Lambda.ArgumentResidualScope
namespace Lamping.Lambda.Labelled

/-- A binder on the actual syntax ancestry, including its real lookup. -/
def BinderAbove (t : LTerm) (p : Path) (l : Label) : Prop :=
  ∃ before after body,p=before++[.body]++after ∧ t.subterm before=some (.lam l body)

/-- SourceSubterm environments contain only original outer binders or actual
binder ancestors. No current-label or graph-origin approximation is used. -/
theorem SourceSubterm.binders_above
    (atSite : SourceSubterm env ctx t p innerEnv innerCtx subtree) :
    ∀ l∈innerEnv,l∈env ∨ BinderAbove t p l := by
  induction atSite with
  | nil => exact fun _ member => .inl member
  | @fn env parent fn q innerEnv innerCtx sub app arg site ih =>
    intro l member
    rcases ih l member with outer | ⟨before,after,body,paths,lookup⟩
    · exact .inl outer
    · exact .inr ⟨.fn::before,after,body,by simp [paths],lookup⟩
  | @arg env parent arg q innerEnv innerCtx sub app fn site ih =>
    intro l member
    rcases ih l member with outer | ⟨before,after,body,paths,lookup⟩
    · exact .inl outer
    · exact .inr ⟨.arg::before,after,body,by simp [paths],lookup⟩
  | @body parent env body q innerEnv innerCtx sub ctx site ih =>
    intro l member
    rcases ih l member with outer | ⟨before,after,b,paths,lookup⟩
    · rcases List.mem_cons.mp outer with equal | outer
      · cases equal
        exact .inr ⟨[],q,body,rfl,rfl⟩
      · exact .inl outer
    · exact .inr ⟨.body::before,after,b,by simp [paths],lookup⟩

/-- An external binder of one actual subtree cannot be a node of another
syntax-disjoint subtree in the same INIT source. -/
theorem SourceSubterm.binder_not_in_disjoint
    (atSite : SourceSubterm [] .external t p env ctx subtree)
    (initial : INIT t) (other : t.subterm q=some sibling)
    (apart : DisjointPositions p q) (member : l∈env) : l∉sibling.labels := by
  intro inside
  have above := atSite.binders_above l member
  rcases above with impossible | ⟨before,after,body,paths,lookup⟩
  · cases impossible
  · obtain ⟨suffix,located⟩ := LTerm.initial_region_locates t initial other lookup inside
    apply apart.2
    refine ⟨suffix++[.body]++after,?_⟩
    simp only [paths,located,List.append_assoc]
/-- App/lambda node identity, retaining binding ports as a distinct port kind. -/
def SourcePort.node : SourcePort → Option Label
  | .appContext l | .appFn l | .appArg l | .lamContext l | .lamBody l | .lamBind l => some l
  | .external | .free _ => none

def SourcePort.Inside (labels : List Label) (port : SourcePort) : Prop :=
  ∃ l∈labels,port.node=some l

theorem SourcePort.Inside.mono {port : SourcePort} (inside : port.Inside labels)
    (subset : ∀ l∈labels,l∈larger) : port.Inside larger := by
  obtain ⟨l,member,node⟩ := inside
  exact ⟨l,subset l member,node⟩

/-- Every real graph turn stays at one actual node and changes the port. -/
theorem SourceTurn.same_node (turn : SourceTurn a b) :
    ∃ l,a.node=some l ∧ b.node=some l := by
  induction turn with
  | appOver l | lamOver l | lamUnder l | appUnder l => exact ⟨l,rfl,rfl⟩
  | symm _ ih => obtain ⟨l,ha,hb⟩ := ih; exact ⟨l,hb,ha⟩

theorem SourceTurn.different (turn : SourceTurn a b) : a≠b := by
  induction turn with
  | appOver | lamOver | lamUnder | appUnder => intro equal; cases equal
  | symm _ ih => exact Ne.symm ih

/-- Every outgoing source port belongs to the subtree or is its exact incoming boundary. -/
theorem sourceEdges_from_port (t : LTerm) (member : e∈sourceEdges env ctx t) :
    e.fromPort=ctx ∨ e.fromPort.Inside t.labels := by
  induction t generalizing env ctx with
  | var l i =>
    have equal : e=sourceEdge env ctx (.var l i) := List.mem_singleton.mp member
    cases equal
    exact .inl rfl
  | lam l b ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact .inl rfl
    · rcases ih member with boundary | inside
      · exact .inr ⟨l,List.mem_cons_self,by simp [boundary,SourcePort.node]⟩
      · exact .inr (SourcePort.Inside.mono inside (fun x hx => List.mem_cons_of_mem _ hx))
  | app l f a hf ha =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact .inl rfl
    · rcases List.mem_append.mp member with left | right
      · rcases hf left with boundary | inside
        · exact .inr ⟨l,List.mem_cons_self,by simp [boundary,SourcePort.node]⟩
        · exact .inr (SourcePort.Inside.mono inside (fun x hx => List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
      · rcases ha right with boundary | inside
        · exact .inr ⟨l,List.mem_cons_self,by simp [boundary,SourcePort.node]⟩
        · exact .inr (SourcePort.Inside.mono inside (fun x hx => List.mem_cons_of_mem _ (List.mem_append_right _ hx)))

/-- Only the incoming root edge can start outside the subtree's own nodes. -/
theorem sourceEdges_nonroot_from (t : LTerm) (member : e∈sourceEdges env ctx t)
    (nonroot : e.atom≠t.label) : e.fromPort.Inside t.labels := by
  cases t with
  | var l i =>
    have equal : e=sourceEdge env ctx (.var l i) := List.mem_singleton.mp member
    cases equal
    exact False.elim (nonroot rfl)
  | lam l b =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact False.elim (nonroot rfl)
    · rcases sourceEdges_from_port b member with boundary | inside
      · exact ⟨l,List.mem_cons_self,by simp [boundary,SourcePort.node]⟩
      · exact SourcePort.Inside.mono inside (fun x hx => List.mem_cons_of_mem _ hx)
  | app l f a =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact False.elim (nonroot rfl)
    · rcases List.mem_append.mp member with left | right
      · rcases sourceEdges_from_port f left with boundary | inside
        · exact ⟨l,List.mem_cons_self,by simp [boundary,SourcePort.node]⟩
        · exact SourcePort.Inside.mono inside (fun x hx => List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      · rcases sourceEdges_from_port a right with boundary | inside
        · exact ⟨l,List.mem_cons_self,by simp [boundary,SourcePort.node]⟩
        · exact SourcePort.Inside.mono inside (fun x hx => List.mem_cons_of_mem _ (List.mem_append_right _ hx))
/-- A variable's original destination is an actual outer binder or a free
port; application/lambda principal destinations are owned by their nodes. -/
theorem sourceBinder_cases (env : List Label) (i : Nat) :
    (∃ l∈env,sourceBinder env i=.lamBind l) ∨ ∃ j,sourceBinder env i=.free j := by
  cases he : env[i]? with
  | none => exact .inr ⟨i-env.length,by simp [sourceBinder,he]⟩
  | some l => exact .inl ⟨l,List.mem_of_getElem? he,by simp [sourceBinder,he]⟩

theorem sourceEdges_to_port (t : LTerm) (member : e∈sourceEdges env ctx t) :
    e.toPort.Inside t.labels ∨ (∃ l∈env,e.toPort=.lamBind l) ∨ ∃ i,e.toPort=.free i := by
  induction t generalizing env ctx with
  | var l i =>
    have equal : e=sourceEdge env ctx (.var l i) := List.mem_singleton.mp member
    cases equal
    exact .inr (sourceBinder_cases env i)
  | lam l b ih =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact .inl ⟨l,List.mem_cons_self,rfl⟩
    · rcases ih member with inside | ⟨binder,outer,port⟩ | free
      · exact .inl (SourcePort.Inside.mono inside (fun x hx => List.mem_cons_of_mem _ hx))
      · rcases List.mem_cons.mp outer with equal | outer
        · cases equal; exact .inl ⟨l,List.mem_cons_self,by simp [port,SourcePort.node]⟩
        · exact .inr (.inl ⟨binder,outer,port⟩)
      · exact .inr (.inr free)
  | app l f a hf ha =>
    rcases List.mem_cons.mp member with equal | member
    · cases equal; exact .inl ⟨l,List.mem_cons_self,rfl⟩
    · rcases List.mem_append.mp member with left | right
      · rcases hf left with inside | outer
        · exact .inl (SourcePort.Inside.mono inside (fun x hx => List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
        · exact .inr outer
      · rcases ha right with inside | outer
        · exact .inl (SourcePort.Inside.mono inside (fun x hx => List.mem_cons_of_mem _ (List.mem_append_right _ hx)))
        · exact .inr outer

/-- INIT label identity and actual disjoint positions give disjoint node sets. -/
theorem LTerm.disjoint_subterm_labels (initial : INIT t)
    (left : t.subterm p=some a) (right : t.subterm q=some b)
    (apart : DisjointPositions p q) : ∀ l∈a.labels,l∉b.labels := by
  intro l member other
  obtain ⟨suffix,node,lookup,equal⟩ := a.label_mem_located member
  have globalLookup : t.subterm (p++suffix)=some node := by
    rw [LTerm.subterm_append,left]
    exact lookup
  obtain ⟨rest,located⟩ := LTerm.initial_region_locates t initial right globalLookup (equal ▸ other)
  have extended := apart.descend_left suffix
  exact extended.2 ⟨rest,located⟩
/-- Ports exposed by an internal nonroot edge. External binding ports are
recorded by their actual syntax environment, rather than declared disjoint. -/
def SubtreePort (env labels : List Label) (port : SourcePort) : Prop :=
  port.Inside labels ∨ (∃ l∈env,port=.lamBind l) ∨ ∃ i,port=.free i

theorem SubtreePort.node_cases (portIn : SubtreePort env labels port)
    (node : port.node=some l) : l∈labels ∨ (l∈env ∧ port=.lamBind l) := by
  rcases portIn with ⟨id,member,equal⟩ | ⟨id,member,equal⟩ | ⟨i,equal⟩
  · have same : id=l := Option.some.inj (equal.symm.trans node)
    exact .inl (same ▸ member)
  · have same : id=l := by simpa [equal,SourcePort.node] using node
    cases same
    exact .inr ⟨member,equal⟩
  · simp [equal,SourcePort.node] at node

/-- Two actual syntax-disjoint subtrees cannot exchange consecutive edges
through a legal turn. Shared external binding vertices do not invalidate it:
both ports would be the same binding port, which a SourceTurn forbids. -/
theorem SourceTurn.not_between_disjoint_subtrees
    (left : SourceSubterm [] .external t p envA ctxA a)
    (right : SourceSubterm [] .external t q envB ctxB b) (initial : INIT t)
    (apart : DisjointPositions p q) (fromLeft : SubtreePort envA a.labels s)
    (fromRight : SubtreePort envB b.labels r) : ¬SourceTurn s r := by
  intro turn
  obtain ⟨node,leftNode,rightNode⟩ := turn.same_node
  rcases fromLeft.node_cases leftNode with inLeft | ⟨outerLeft,leftPort⟩
  · rcases fromRight.node_cases rightNode with inRight | ⟨outerRight,rightPort⟩
    · exact LTerm.disjoint_subterm_labels initial left.lookup right.lookup apart node inLeft inRight
    · exact right.binder_not_in_disjoint initial left.lookup apart.symm outerRight inLeft
  · rcases fromRight.node_cases rightNode with inRight | ⟨outerRight,rightPort⟩
    · exact left.binder_not_in_disjoint initial right.lookup apart outerLeft inRight
    · exact turn.different (leftPort.trans rightPort.symm)

/-- Both endpoints of a nonroot subtree edge have the classifications above,
with the orientation retained even when the edge is traversed backwards. -/
theorem SourceTraverse.subtree_ports (traverse : SourceTraverse (sourceEdges env ctx t) a e b)
    (nonroot : Label.atom e.atom≠t.label) :
    SubtreePort env t.labels a ∧ SubtreePort env t.labels b := by
  cases traverse with
  | @forward edge n member atomic =>
    have fromInside := sourceEdges_nonroot_from t member (by simpa [atomic] using nonroot)
    exact ⟨.inl fromInside,sourceEdges_to_port t member⟩
  | @backward edge n member atomic =>
    have fromInside := sourceEdges_nonroot_from t member (by simpa [atomic] using nonroot)
    exact ⟨sourceEdges_to_port t member,.inl fromInside⟩

/-- A concrete adjacent pair of internal edges in two distinct copies is
impossible, including when both variable edges meet the same outer binder. -/
theorem SourceTraverse.no_cross_copy_turn
    (left : SourceSubterm [] .external t p envA ctxA a)
    (right : SourceSubterm [] .external t q envB ctxB b) (initial : INIT t)
    (apart : DisjointPositions p q)
    (first : SourceTraverse (sourceEdges envA ctxA a) s edgeA middleA)
    (second : SourceTraverse (sourceEdges envB ctxB b) middleB edgeB r)
    (notRootA : Label.atom edgeA.atom≠a.label) (notRootB : Label.atom edgeB.atom≠b.label) :
    ¬SourceTurn middleA middleB :=
  SourceTurn.not_between_disjoint_subtrees left right initial apart
    (first.subtree_ports notRootA).2 (second.subtree_ports notRootB).1
/-- The ends of an internal-edge walk retain the actual subtree boundary
classification. Nonempty paths are represented by SourceWalk itself. -/
theorem SourceWalk.subtree_ports (walk : SourceWalk (sourceEdges env ctx t) a word b)
    (nonroot : ∀ e∈word,Label.atom e.atom≠t.label) :
    SubtreePort env t.labels a ∧ SubtreePort env t.labels b := by
  induction walk with
  | edge traverse => exact traverse.subtree_ports (nonroot _ List.mem_cons_self)
  | @join start first middle next rest finish hp turn hq ihp ihq =>
    exact ⟨(ihp (fun e he => nonroot e (List.mem_append_left _ he))).1,
      (ihq (fun e he => nonroot e (List.mem_append_right _ he))).2⟩

/-- Actual syntax-disjoint components cannot be mixed by a supported walk.
The cover concerns each actual traversal, with its signed edge and endpoints;
it is not a same-copy conclusion or an unproved path-reflection premise. -/
theorem SourceWalk.one_component {Index : Type} {sites : Index → Path}
    {environments : Index → List Label} {contexts : Index → SourcePort}
    {subtrees : Index → LTerm}
    (components : ∀ i,SourceSubterm [] .external t (sites i) (environments i) (contexts i) (subtrees i))
    (initial : INIT t) (separate : ∀ i j,i≠j → DisjointPositions (sites i) (sites j))
    (walk : SourceWalk (sourceEdges [] .external t) a word b)
    (cover : ∀ {s e r},e∈word → SourceTraverse (sourceEdges [] .external t) s e r →
      ∃ i,SourceTraverse (sourceEdges (environments i) (contexts i) (subtrees i)) s e r ∧
        Label.atom e.atom≠(subtrees i).label) :
    ∃ i,SourceWalk (sourceEdges (environments i) (contexts i) (subtrees i)) a word b ∧
      ∀ e∈word,Label.atom e.atom≠(subtrees i).label := by
  classical
  induction walk with
  | edge traverse =>
    obtain ⟨i,localEdge,notRoot⟩ := cover List.mem_cons_self traverse
    exact ⟨i,.edge localEdge,by intro e member; exact List.mem_singleton.mp member ▸ notRoot⟩
  | @join start first middle next rest finish hp turn hq ihp ihq =>
    obtain ⟨i,leftWalk,leftNotRoot⟩ := ihp (fun member edge => cover (List.mem_append_left _ member) edge)
    obtain ⟨j,rightWalk,rightNotRoot⟩ := ihq (fun member edge => cover (List.mem_append_right _ member) edge)
    have same : i=j := by
      by_cases same : i=j
      · exact same
      · exact False.elim (SourceTurn.not_between_disjoint_subtrees (components i) (components j)
          initial (separate i j same) (leftWalk.subtree_ports leftNotRoot).2
          (rightWalk.subtree_ports rightNotRoot).1 turn)
    cases same
    exact ⟨i,.join leftWalk turn rightWalk,by
      intro e member
      rcases List.mem_append.mp member with left | right
      · exact leftNotRoot e left
      · exact rightNotRoot e right⟩
end Lamping.Lambda.Labelled