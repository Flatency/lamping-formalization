import Lamping.Lambda.SourceBinderOccurrences
import Lamping.Lamping.MatchingSourceEdges
import Lamping.Lamping.MatchingRedexConnection
namespace Lamping.Lambda.Labelled
/-- Every listed original edge is attached to its actual occurrence,
including the real variable environment. No label uniqueness is required. -/
theorem sourceEdges_occurrence (original : LTerm) (member : edge∈sourceEdges env ctx original) :
    ∃ p innerEnv innerCtx sub,SourceSubterm env ctx original p innerEnv innerCtx sub ∧
      sourceEdge innerEnv innerCtx sub=edge := by
  induction original generalizing env ctx with
  | var label index =>
    simp only [sourceEdges,List.mem_singleton] at member
    exact ⟨[],env,ctx,_,.nil,member.symm⟩
  | lam label body ih =>
    simp only [sourceEdges,List.mem_cons] at member
    rcases member with equal | below
    · exact ⟨[],env,ctx,_,.nil,equal.symm⟩
    · obtain ⟨p,innerEnv,innerCtx,sub,site,eq⟩ := ih below
      exact ⟨.body::p,innerEnv,innerCtx,sub,.body site,eq⟩
  | app label fn arg hf ha =>
    simp only [sourceEdges,List.mem_cons,List.mem_append] at member
    rcases member with equal | left | right
    · exact ⟨[],env,ctx,_,.nil,equal.symm⟩
    · obtain ⟨p,innerEnv,innerCtx,sub,site,eq⟩ := hf left
      exact ⟨.fn::p,innerEnv,innerCtx,sub,.fn site,eq⟩
    · obtain ⟨p,innerEnv,innerCtx,sub,site,eq⟩ := ha right
      exact ⟨.arg::p,innerEnv,innerCtx,sub,.arg site,eq⟩
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
/-- Source occurrence/port evidence for a physical endpoint. This relation
is constructed below; a repeated source label alone does not make it a map. -/
inductive SourcePortRealizes (original : LTerm) (g : Net signature N B W) (root : B) :
    SourcePort → Endpoint g → Prop where
  | external : SourcePortRealizes original g root .external (.inr (.inl root))
  | departure (lookup : original.subterm p=some term) (sourceRole : SourceDeparture term step sourcePort)
      (parent : RootAccess g root) (word : accessWord g parent.val=p)
      (roles : SyntaxChildPorts (g.label node).sort ctx departure step)
      (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
      SourcePortRealizes original g root sourcePort (.inl ⟨node,departure⟩)
  | appContext (lookup : original.subterm p=some (.app origin fn arg))
      (access : RootAccess g root) (word : accessWord g access.val=p)
      (shape : (g.label node).sort=.op .app) (role : HEq port appCtx)
      (finish : access.val.getLast?=some (g.wire (.inl ⟨node,port⟩))) :
      SourcePortRealizes original g root (.appContext origin) (.inl ⟨node,port⟩)
  | lamContext (lookup : original.subterm p=some (.lam origin body))
      (access : RootAccess g root) (word : accessWord g access.val=p)
      (shape : (g.label node).sort=.op .lam) (role : HEq port (Sum.inl () : Port (.op .lam)))
      (finish : access.val.getLast?=some (g.wire (.inl ⟨node,port⟩))) :
      SourcePortRealizes original g root (.lamContext origin) (.inl ⟨node,port⟩)
  | binding (lookup : original.subterm p=some (.lam origin body))
      (parent : RootAccess g root) (word : accessWord g parent.val=p)
      (shape : (g.label node).sort=.op .lam) (contextRole : HEq ctx (Sum.inl () : Port (.op .lam)))
      (bindingRole : HEq port lamBind)
      (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
      SourcePortRealizes original g root (.lamBind origin) (.inl ⟨node,port⟩)
end
private def sourceDepartureToken : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem SyntaxChildPorts.departure_token {kind : Kind} {ctx departure : Port kind}
    (roles : SyntaxChildPorts kind ctx departure step) : sourceDepartureToken kind departure=[step] := by
  cases roles <;> rfl
private theorem SyntaxChildPorts.function_context {kind : Kind} {ctx departure : Port kind}
    (roles : SyntaxChildPorts kind ctx departure .fn) : kind=.op .app ∧ HEq ctx appCtx := by
  cases roles
  exact ⟨rfl,HEq.rfl⟩
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
private theorem Matches.labelled_lookup_kind {original term : LTerm}
    (matching : Matches g root original.erase) (access : RootAccess g root)
    (word : accessWord g access.val=p) (lookup : original.subterm p=some term) :
    accessKind g access.val=some (syntaxShape term.erase).kind := by
  obtain ⟨bijection,corresponds,_⟩ := matching
  obtain ⟨positionWord,u,atPosition,observation⟩ := corresponds access
  have actual : subtermAt original.erase (bijection access).val=some term.erase := by
    rw [←positionWord,word,←LTerm.erase_subterm,lookup]
    rfl
  have equal : u=term.erase := Option.some.inj (atPosition.symm.trans actual)
  subst u
  exact observation.1
/-- The target of one actual source edge has a real physical endpoint. The
closed-source hypothesis discharges free-variable terminals only here; no
open graph correctness claim is hidden in SourcePortRealizes. -/
theorem Matches.source_edge_terminal {original sub : LTerm}
    (matching : Matches g root original.erase) (closed : Closed original.erase)
    (site : SourceSubterm [] .external original p env ctx sub)
    (access : RootAccess g root) (word : accessWord g access.val=p) :
    ∃ target,SourcePortRealizes original g root (sourceEdge env ctx sub).toPort target ∧
      access.val.getLast?=some (g.wire target) := by
  cases sub with
  | app origin fn arg =>
    have atFunction : original.subterm (p++[.fn])=some fn := by
      rw [LTerm.subterm_append,site.lookup]
      cases fn <;> rfl
    let childPosition : Position original.erase := ⟨p++[.fn],by
      rw [←LTerm.erase_subterm,atFunction]; rfl⟩
    obtain ⟨child,childWord,_⟩ := Matches.observation g matching childPosition
    obtain ⟨node,actualCtx,departure,_,roles,finish,_,_,_⟩ :=
      matching.syntax_child_fragment access child .fn (by simpa only [word] using childWord)
    obtain ⟨shape,contextRole⟩ := roles.function_context
    exact ⟨_,.appContext site.lookup access word shape contextRole finish,finish⟩
  | lam origin body =>
    have kind : accessKind g access.val=some .lam := matching.labelled_lookup_kind access word site.lookup
    obtain ⟨node,port,index,label,role,finish⟩ := access.lambda_endpoint kind
    have shape : (g.label node).sort=.op .lam := congrArg (fun actual => actual.sort) label
    exact ⟨_,.lamContext site.lookup access word shape role finish,finish⟩
  | var variableLabel index =>
    have actualLookup : subtermAt original.erase p=some (.var index) := by
      rw [←LTerm.erase_subterm,site.lookup]; rfl
    have scoping := scoped_subterm closed actualLookup
    have inEnv : index<env.length := by
      rw [site.env_length]
      exact scoping
    let origin := env[index]
    have entry : env[index]?=some origin := List.getElem?_eq_getElem inEnv
    have bound : sourceBinder env index=.lamBind origin := by simp only [sourceBinder,entry]
    obtain ⟨parent,loop,a,b,c,binding,actualCtx,body,split,contextRole,finish,_,oldBinder,_,_⟩ :=
      matching.original_source_binder site bound access word
    have last : access.val.getLast?=some (g.wire (.inl ⟨binding.binder,binding.bind⟩)) := by
      rw [split,List.getLast?_append,binding.finish]
      rfl
    refine ⟨_,?_,last⟩
    change SourcePortRealizes original g root (sourceBinder env index) _
    rw [bound]
    exact .binding oldBinder parent rfl binding.isLam contextRole binding.bind_role finish
end
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
/-- One actual original edge is realized by a literal fragment of an actual
source root access, with occurrence-based port witnesses and original labels. -/
structure SourceEdgeFragment (original : LTerm) (g : Net signature N B W) (root : B)
    (edge : SourceEdge) (p : Path) where
  access : RootAccess g root
  word : accessWord g access.val=p
  occurrence : ∃ env ctx sub,SourceSubterm [] .external original p env ctx sub ∧ sourceEdge env ctx sub=edge
  before : List (Endpoint g)
  segments : List (Endpoint g)
  fromEndpoint : Endpoint g
  toEndpoint : Endpoint g
  fromRealizes : SourcePortRealizes original g root edge.fromPort fromEndpoint
  toRealizes : SourcePortRealizes original g root edge.toPort toEndpoint
  literal : access.val=before++segments
  start : segments.head?=some fromEndpoint
  finish : segments.getLast?=some (g.wire toEndpoint)
  forward : Forward g segments
  emptyWord : accessWord g segments=[]
  assignments : ∀ a b,Labelling g access.val a b → ∃ middle,
    (before=[] ∧ middle=a ∨ Labelling g before a middle) ∧ Labelling g segments middle b
end
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
/-- Full base-edge realization. The caller supplies only actual source
Matches, closed syntax and a genuine old occurrence, never an endpoint map. -/
theorem Matches.base_source_edge_fragment {original sub : LTerm}
    (matching : Matches g root original.erase) (closed : Closed original.erase)
    (site : SourceSubterm [] .external original p env ctx sub) :
    Nonempty (SourceEdgeFragment original g root (sourceEdge env ctx sub) p) := by
  let position : Position original.erase := ⟨p,by rw [←LTerm.erase_subterm,site.lookup]; rfl⟩
  obtain ⟨access,word,_⟩ := Matches.observation g matching position
  obtain ⟨terminal,realizes,finish⟩ := matching.source_edge_terminal closed site access word
  have sourceFrom : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
  rcases site.last_departure with ⟨empty,context⟩ | ⟨parentPath,step,term,atChild,atParent,sourceRole⟩
  · refine ⟨{
      access := access
      word := word
      occurrence := ⟨env,ctx,sub,site,rfl⟩
      before := []
      segments := access.val
      fromEndpoint := .inr (.inl root)
      toEndpoint := terminal
      fromRealizes := ?_
      toRealizes := realizes
      literal := rfl
      start := access.property.2.1
      finish := finish
      forward := access.property.1.2
      emptyWord := word.trans empty
      assignments := ?_ }⟩
    · rw [sourceFrom,context]
      exact .external
    · intro a b labels
      exact ⟨a,Or.inl ⟨rfl,rfl⟩,labels⟩
  · let parentPosition : Position original.erase := ⟨parentPath,by
      rw [←LTerm.erase_subterm,atParent]; rfl⟩
    obtain ⟨parent,parentWord,_⟩ := Matches.observation g matching parentPosition
    have childWord : accessWord g access.val=accessWord g parent.val++[step] := by
      rw [word,parentWord]
      exact atChild
    obtain ⟨node,physicalCtx,departure,tail,roles,parentFinish,split,forward,assignments⟩ :=
      matching.syntax_child_fragment parent access step childWord
    have token : arrivalWord g (.inl ⟨node,departure⟩)=[step] := roles.departure_token
    have noTokens : accessWord g ((.inl ⟨node,departure⟩)::tail)=[] := by
      have tokens := childWord
      rw [split,accessWord_append g parent.val _ parent.property.1.1.walk.nonempty,
        List.flatMap_cons,token] at tokens
      have after := List.append_cancel_left tokens
      exact (List.cons.inj (by simpa only [List.singleton_append] using after)).2
    have fragmentFinish : ((.inl ⟨node,departure⟩)::tail).getLast?=some (g.wire terminal) := by
      rw [split,List.getLast?_append] at finish
      simpa only [List.getLast?_cons,Option.some_or] using finish
    refine ⟨{
      access := access
      word := word
      occurrence := ⟨env,ctx,sub,site,rfl⟩
      before := parent.val
      segments := (.inl ⟨node,departure⟩)::tail
      fromEndpoint := .inl ⟨node,departure⟩
      toEndpoint := terminal
      fromRealizes := ?_
      toRealizes := realizes
      literal := split
      start := rfl
      finish := fragmentFinish
      forward := forward
      emptyWord := noTokens
      assignments := ?_ }⟩
    · rw [sourceFrom]
      exact .departure atParent sourceRole parent parentWord roles parentFinish
    · intro a b labels
      obtain ⟨middle,before,after⟩ := assignments a b labels
      exact ⟨middle,Or.inr before,after⟩

/-- Direct base case for the atom constructor of SourceRoute: actual edge
membership is enough to construct its actual physical fragment. -/
theorem Matches.source_edge_member_fragment {original : LTerm}
    (matching : Matches g root original.erase) (closed : Closed original.erase)
    (member : edge∈sourceEdges [] .external original) :
    ∃ p,Nonempty (SourceEdgeFragment original g root edge p) := by
  obtain ⟨p,env,ctx,sub,site,equal⟩ := sourceEdges_occurrence original member
  rw [←equal]
  exact ⟨p,matching.base_source_edge_fragment closed site⟩
/-- Reversal retains every actual segment occurrence, swaps the two source
port witnesses, and uses the original assignment in the opposite direction.
It is not claimed to be a forward root access. -/
theorem SourceEdgeFragment.reverse_endpoints
    (fragment : SourceEdgeFragment original g root edge p) :
    (reverseEdges fragment.segments).head?=some fragment.toEndpoint ∧
      (reverseEdges fragment.segments).getLast?=some (g.wire fragment.fromEndpoint) := by
  constructor
  · simp only [reverseEdges,List.head?_map,List.head?_reverse,fragment.finish,Option.map_some,Pairing.involutive]
  · simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,fragment.start,Option.map_some]

theorem SourceEdgeFragment.reverse_assignment
    (fragment : SourceEdgeFragment original g root edge p) (labels : Labelling g fragment.access.val a b) :
    ∃ middle,(fragment.before=[] ∧ middle=a ∨ Labelling g fragment.before a middle) ∧
      Labelling g (reverseEdges fragment.segments) b middle := by
  obtain ⟨middle,before,after⟩ := fragment.assignments a b labels
  exact ⟨middle,before,after.reverse⟩
end
end Lamping.AG





