import Lamping.Lamping.PhysicalReadingRoles
import Lamping.Lamping.ActualPrerequisiteSignedSlots
namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {current oldSource : LTerm}
variable {F ps : List Path} {degree : Label}
variable {leftStart rightStart : Path} {leftEdges rightEdges : List Path}
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

private theorem walk_read_at {t : LTerm} {first : ProperPosition t}
    {edges : List Path} {signs : List Bool} {vertices : List (ProperPosition t)}
    (walk : SignedProperWalk t first edges signs vertices) (k : Nat) (bound : k<edges.length) :
    ∃a b forward,vertices[k]?=some a ∧vertices[k+1]?=some b ∧signs[k]?=some forward ∧
      PrerequisiteReadsDirected t a.val edges[k] forward ∧
      (if forward then Source t edges[k] (some a) ∧Target t edges[k] (some b)
       else Target t edges[k] (some a) ∧Source t edges[k] (some b)) := by
  induction walk generalizing k with
  | nil => simp at bound
  | @cons a b edge edges signs vertices forward reading step tail ih =>
    cases k with
    | zero =>
      have first : vertices[0]?=some b := by cases tail <;> rfl
      exact ⟨a,b,forward,rfl,by simpa using first,rfl,reading,step⟩
    | succ k =>
      have small : k<edges.length := by simp only [List.length_cons] at bound;omega
      obtain ⟨c,d,f,ca,da,fa,actual,incidence⟩ := ih k small
      exact ⟨c,d,f,by simpa using ca,by simpa [Nat.succ_eq_add_one,Nat.add_assoc] using da,
        by simpa using fa,actual,incidence⟩

private theorem read_node {t : LTerm}
    (read : PrerequisiteReadsDirected t reader edge forward) : ∃node,t.subterm edge=some node := by
  rcases read.1 with ⟨a,fn,arg,lookup,equal⟩ |⟨a,body,lookup,equal⟩
  · refine ⟨fn,?_⟩;rw [equal,LTerm.subterm_append,lookup];cases fn <;> rfl
  · exact ⟨_,equal ▸ lookup⟩

private theorem nonlast_not_redex {t : LTerm} {edges : List Path}
    (chain : PrerequisiteChain t start edges) (k : Nat) (bound : k+1<edges.length) :
    ¬PrerequisiteRedexEdge t edges[k] := by
  obtain ⟨front,last,split,_redex,earlier⟩ := chain.redex_only_last
  have sizes := congrArg List.length split
  simp only [List.length_append,List.length_singleton] at sizes
  have small : k<front.length := by omega
  have bound' : k<edges.length := by omega
  have get : edges[k]?=front[k]? := by rw [split,List.getElem?_append_left small]
  have same : edges[k]=front[k] := by
    exact Option.some.inj (by simpa only [List.getElem?_eq_getElem bound',List.getElem?_eq_getElem small] using get)
  rw [same]
  exact earlier _ (List.getElem_mem small)

private theorem incidence_far_kinds
    {le re : Path} {ln rn : LTerm} {a b c d : ProperPosition current} {forward : Bool}
    (leftLookup : current.subterm le=some ln) (rightLookup : current.subterm re=some rn)
    (roles : le.getLast?=re.getLast?) (targets : targetApp ln=targetApp rn)
    (leftStep : if forward then Source current le (some a) ∧Target current le (some b)
      else Target current le (some a) ∧Source current le (some b))
    (rightStep : if forward then Source current re (some c) ∧Target current re (some d)
      else Target current re (some c) ∧Source current re (some d)) :
    ∃kind,ProperKind current b kind ∧ProperKind current d kind := by
  cases forward with
  | false =>
    obtain ⟨ls,ll,lk⟩ := Source.actual_kind leftStep.2
    obtain ⟨rs,rl,rk⟩ := Source.actual_kind rightStep.2
    have steps : ls=rs := Option.some.inj (ll.symm.trans (roles.trans rl))
    subst rs
    exact ⟨departureApp ls,lk,rk⟩
  | true =>
    refine ⟨targetApp ln,Target.actual_kind leftStep.2 leftLookup,?_⟩
    rw [targets];exact Target.actual_kind rightStep.2 rightLookup

theorem actual_terminal_predecessor_direction_eq
    (matching : Matches g root current.erase)
    (selection : OccurrenceFragmentSelection current g root)
    (leftParent : PrerequisiteChain current leftStart leftEdges)
    (rightParent : PrerequisiteChain current rightStart rightEdges)
    (physical : SameChainRepresentation selection leftParent rightParent)
    (left : ActualUnsafeMarkerCut F ps oldSource current degree leftStart leftEdges)
    (right : ActualUnsafeMarkerCut F ps oldSource current degree rightStart rightEdges)
    (ordinal : left.before.length=right.before.length)
    (positive : 0<left.before.length)
    (leftTerminal : left.after=[]) (rightTerminal : right.after=[]) :
    left.forward=right.forward := by
  let k := left.before.length-1
  have next : k+1=left.before.length := by dsimp [k];omega
  have leftSize : leftEdges.length=left.before.length+1 := by
    have sizes:=congrArg List.length left.split
    simpa only [leftTerminal,List.length_append,List.length_cons,List.length_nil,Nat.add_zero] using sizes
  have rightSize : rightEdges.length=right.before.length+1 := by
    have sizes:=congrArg List.length right.split
    simpa only [rightTerminal,List.length_append,List.length_cons,List.length_nil,Nat.add_zero] using sizes
  have leftBound : k<leftEdges.length := by omega
  have rightBound : k<rightEdges.length := by omega
  obtain ⟨lf,ss,vs,lt,lwalk⟩ := leftParent.signed_path
  obtain ⟨rf,ts,ws,rt,rwalk⟩ := rightParent.signed_path
  obtain ⟨la,lb,ld,_laAt,lbAt,_ldAt,lread,lstep⟩ := walk_read_at lwalk k leftBound
  obtain ⟨ra,rb,rd,_raAt,rbAt,_rdAt,rread,rstep⟩ := walk_read_at rwalk k rightBound
  obtain ⟨ln,lnAt⟩ := read_node lread
  obtain ⟨rn,rnAt⟩ := read_node rread
  let lp : Position current.erase := ⟨leftEdges[k],by rw [←LTerm.erase_subterm,lnAt];rfl⟩
  let rp : Position current.erase := ⟨rightEdges[k],by rw [←LTerm.erase_subterm,rnAt];rfl⟩
  have lslot : leftEdges[k]?=some lp.val := by simp only [lp,List.getElem?_eq_getElem leftBound]
  have rslot : rightEdges[k]?=some rp.val := by simp only [rp,List.getElem?_eq_getElem rightBound]
  have pieces := same_chain_representation_slot selection leftParent rightParent physical lp rp lslot rslot
  have lnonroot : lp.val≠[] := leftParent.reading_ne_nil (List.getElem_mem leftBound)
  have rnonroot : rp.val≠[] := rightParent.reading_ne_nil (List.getElem_mem rightBound)
  have roles := same_incoming_roles matching (selection lp) (selection rp) lnonroot rnonroot pieces
  have targets := same_terminal_kind matching (selection lp) (selection rp) lnAt rnAt pieces
  have lnonredex := nonlast_not_redex leftParent k (by omega)
  have rnonredex := nonlast_not_redex rightParent k (by omega)
  have signs := lread.nonredex_direction_eq rread lnonredex rnonredex roles
  have rstep' : if ld then Source current rightEdges[k] (some ra) ∧Target current rightEdges[k] (some rb)
      else Target current rightEdges[k] (some ra) ∧Source current rightEdges[k] (some rb) := by
    rw [signs];exact rstep
  obtain ⟨kind,lk,rk⟩ := incidence_far_kinds lnAt rnAt roles targets lstep rstep'
  obtain ⟨lr,lrPath,lrAt,_lrSign⟩ := left.signed_slot lwalk lt
  obtain ⟨rr,rrPath,rrAt,_rrSign⟩ := right.signed_slot rwalk rt
  rw [next] at lbAt
  rw [next,ordinal] at rbAt
  have lbEq : lb=lr := Option.some.inj (lbAt.symm.trans lrAt)
  have rbEq : rb=rr := Option.some.inj (rbAt.symm.trans rrAt)
  have lreading : PrerequisiteReadsDirected current lr.val left.edge left.forward := by
    rw [lrPath];exact left.reading
  have rreading : PrerequisiteReadsDirected current rr.val right.edge right.forward := by
    rw [rrPath];exact right.reading
  have lkind : ProperKind current lr kind := lbEq ▸ lk
  have rkind : ProperKind current rr kind := rbEq ▸ rk
  exact (lkind.unique lreading.proper_kind).symm.trans (rkind.unique rreading.proper_kind)

#print axioms actual_terminal_predecessor_direction_eq
end
end Lamping.AG
