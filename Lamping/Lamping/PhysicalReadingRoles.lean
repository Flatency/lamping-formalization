import Lamping.Lamping.ActualAfterRepresentation
import Lamping.Lamping.CanonicalAfterFarComparison
import Lamping.Lamping.FragmentChildStepSeparation
import Lamping.Lamping.FanAppReadDispatcher

namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

private theorem departure_metadata
    (matching : Matches g root current.erase)
    (fragment : OccurrenceFragment current g root p) (nonroot : p≠[]) :
    ∃(term : LTerm) (step : Step) (parent : RootAccess g root),
      SourceDeparture term step (sourceEdge fragment.environment fragment.context fragment.term).fromPort ∧
      p=accessWord g parent.val++[step] ∧p.getLast?=some step := by
  rcases fragment with ⟨sub,env,ctx,occurrence,fragment⟩
  rcases occurrence.last_departure with ⟨empty,_external⟩|⟨parentPath,step,term,split,lookup,role⟩
  · exact False.elim (nonroot empty)
  · let position : Position current.erase := ⟨parentPath,by rw [←LTerm.erase_subterm,lookup];rfl⟩
    obtain ⟨parent,word,_⟩ := Matches.observation g matching position
    have sourceFrom : (sourceEdge env ctx sub).fromPort=ctx := by cases sub <;> rfl
    refine ⟨term,step,parent,?_,?_,?_⟩
    · rw [sourceFrom];exact role
    · rw [word];exact split
    · rw [split];simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]

private theorem same_incoming_roles
    (matching : Matches g root current.erase)
    (left : OccurrenceFragment current g root p) (right : OccurrenceFragment current g root q)
    (leftNonroot : p≠[]) (rightNonroot : q≠[])
    (same : left.fragment.segments=right.fragment.segments) : p.getLast?=q.getLast? := by
  obtain ⟨lt,ls,lp,lr,lw,ll⟩ := departure_metadata matching left leftNonroot
  obtain ⟨rt,rs,rp,rr,rw,rl⟩ := departure_metadata matching right rightNonroot
  have step := left.fragment.child_step_eq_of_segments_eq matching right.fragment lr rr lp rp lw rw same
  exact ll.trans ((congrArg some step).trans rl.symm)

private theorem nonterminal_not_redex
    (chain : PrerequisiteChain current reader (edge::after)) (more : after≠[]) :
    ¬PrerequisiteRedexEdge current edge := by
  obtain ⟨before,last,split,_redex,earlier⟩ := chain.redex_only_last
  cases before with
  | nil =>
    simp only [List.nil_append,List.cons.injEq] at split
    exact False.elim (more split.2)
  | cons head tail =>
    have eq : edge=head := (List.cons.inj split).1
    exact earlier edge (by rw [eq];exact List.mem_cons_self)

private theorem lookup_access_kind
    (matching : Matches g root current.erase)
    (access : RootAccess g root) (word : accessWord g access.val=p)
    (lookup : current.subterm p=some node) :
    accessKind g access.val=some (syntaxShape node.erase).kind := by
  obtain ⟨bijection,corresponds,_⟩ := matching
  obtain ⟨positionWord,u,atPosition,observation⟩ := corresponds access
  have actual : subtermAt current.erase (bijection access).val=some node.erase := by
    rw [←positionWord,word,←LTerm.erase_subterm,lookup];rfl
  have equal : u=node.erase := Option.some.inj (atPosition.symm.trans actual)
  subst u
  exact observation.1

private theorem same_terminal_kind
    (matching : Matches g root current.erase)
    (left : OccurrenceFragment current g root p) (right : OccurrenceFragment current g root q)
    (leftLookup : current.subterm p=some ln) (rightLookup : current.subterm q=some rn)
    (same : left.fragment.segments=right.fragment.segments) : targetApp ln=targetApp rn := by
  have kinds := left.fragment.access_kind_eq_of_segments_eq right.fragment same
  rw [lookup_access_kind matching left.fragment.access left.fragment.word leftLookup,
    lookup_access_kind matching right.fragment.access right.fragment.word rightLookup] at kinds
  have equal := Option.some.inj kinds
  cases ln <;> cases rn <;> simp_all [syntaxShape,LTerm.erase,AccessShape.kind,targetApp]

private theorem far_kinds
    (leftLookup : current.subterm le=some ln) (rightLookup : current.subterm re=some rn)
    (roles : le.getLast?=re.getLast?) (targets : targetApp ln=targetApp rn)
    (ls : IncomingIncidenceSnapshot current le) (rs : IncomingIncidenceSnapshot current re)
    (lf : ls.far forward=some lv) (rf : rs.far forward=some rv) :
    ∃kind,ProperKind current lv kind ∧ProperKind current rv kind := by
  cases forward with
  | false =>
    change ls.fromVertex=some lv at lf
    change rs.fromVertex=some rv at rf
    have leftSource : Source current le (some lv) := lf ▸ ls.fromSpec
    have rightSource : Source current re (some rv) := rf ▸ rs.fromSpec
    obtain ⟨lstep,ll,lk⟩ := Source.actual_kind leftSource
    obtain ⟨rstep,rl,rk⟩ := Source.actual_kind rightSource
    have steps : lstep=rstep := Option.some.inj (ll.symm.trans (roles.trans rl))
    subst rstep
    exact ⟨departureApp lstep,lk,rk⟩
  | true =>
    change ls.toVertex=some lv at lf
    change rs.toVertex=some rv at rf
    have leftTarget : Target current le (some lv) := lf ▸ ls.toSpec
    have rightTarget : Target current re (some rv) := rf ▸ rs.toSpec
    refine ⟨targetApp ln,Target.actual_kind leftTarget leftLookup,?_⟩
    rw [targets]
    exact Target.actual_kind rightTarget rightLookup

private theorem actual_snapshot (closed : Closed current.erase)
    (lookup : current.subterm edge=some node) : Nonempty (IncomingIncidenceSnapshot current edge) := by
  let position : Edge current := ⟨edge,by rw [←LTerm.erase_subterm,lookup];rfl⟩
  obtain ⟨fromVertex,fromSpec⟩ := source_total current position
  obtain ⟨toVertex,toSpec⟩ := target_total current closed position
  exact ⟨⟨fromVertex,toVertex,fromSpec,toSpec⟩⟩

private theorem slot_at_split {edges before after : List Path} {edge : Path}
    (split : edges=before++edge::after) : edges[before.length]?=some edge := by
  rw [split,List.getElem?_append_right (by omega)]
  simp

private theorem cut_slot
    {F ps : List Path} {source : LTerm} {degree : Label} {start : Path} {edges : List Path}
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges) :
    edges[cut.before.length]?=some cut.edge := slot_at_split cut.split

theorem actual_parent_cut_physical_reading_roles
    {F ps : List Path} {source : LTerm} {degree : Label}
    {leftStart rightStart : Path} {es fs : List Path}
    (matching : Matches g root current.erase)
    (sourceClosed : Closed source.erase)
    (labels : History ps source current)
    (selection : OccurrenceFragmentSelection current g root)
    (leftParent : PrerequisiteChain current leftStart es)
    (rightParent : PrerequisiteChain current rightStart fs)
    (physical : SameChainRepresentation selection leftParent rightParent)
    (left : ActualUnsafeMarkerCut F ps source current degree leftStart es)
    (right : ActualUnsafeMarkerCut F ps source current degree rightStart fs)
    (sameBefore : left.before.length=right.before.length)
    (nonempty : left.after≠[]) :
    right.after≠[] ∧left.forward=right.forward ∧
      ∃ (leftSnapshot : IncomingIncidenceSnapshot current left.edge)
        (rightSnapshot : IncomingIncidenceSnapshot current right.edge)
        (leftFar : CanonicalAfterFarOutput labels left leftSnapshot)
        (rightFar : CanonicalAfterFarOutput labels right rightSnapshot),
        ∃kind : Bool,
          ProperKind current leftFar.currentProper kind ∧
          ProperKind current rightFar.currentProper kind := by
  obtain ⟨rightMore,_⟩ := actual_cut_after_same_representation selection leftParent rightParent physical
    left right sameBefore nonempty
  let lp : Position current.erase := ⟨left.edge,by rw [←LTerm.erase_subterm,left.lookup];rfl⟩
  let rp : Position current.erase := ⟨right.edge,by rw [←LTerm.erase_subterm,right.lookup];rfl⟩
  have ls : es[left.before.length]?=some lp.val := cut_slot left
  have rs : fs[left.before.length]?=some rp.val := by rw [sameBefore];exact cut_slot right
  have pieces := same_chain_representation_slot selection leftParent rightParent physical lp rp ls rs
  have leftNonroot : left.edge≠[] := left.remaining.reading_ne_nil List.mem_cons_self
  have rightNonroot : right.edge≠[] := right.remaining.reading_ne_nil List.mem_cons_self
  have roles := same_incoming_roles matching (selection lp) (selection rp) leftNonroot rightNonroot pieces
  have direction := left.reading.nonredex_direction_eq right.reading
    (nonterminal_not_redex left.remaining nonempty) (nonterminal_not_redex right.remaining rightMore) roles
  have targets := same_terminal_kind matching (selection lp) (selection rp) left.lookup right.lookup pieces
  obtain ⟨leftSnapshot⟩ := actual_snapshot (labels.closed sourceClosed) left.lookup
  obtain ⟨rightSnapshot⟩ := actual_snapshot (labels.closed sourceClosed) right.lookup
  obtain ⟨leftFar⟩ := left.canonical_far_output labels sourceClosed nonempty leftSnapshot
  obtain ⟨rightFar⟩ := right.canonical_far_output labels sourceClosed rightMore rightSnapshot
  have rightEq : rightSnapshot.far left.forward=some rightFar.currentProper := by
    rw [direction];exact rightFar.farEq
  exact ⟨rightMore,direction,leftSnapshot,rightSnapshot,leftFar,rightFar,
    far_kinds left.lookup right.lookup roles targets leftSnapshot rightSnapshot leftFar.farEq rightEq⟩
end
#print axioms actual_parent_cut_physical_reading_roles
end Lamping.AG
