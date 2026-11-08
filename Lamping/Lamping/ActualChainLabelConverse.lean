import Lamping.Lamping.ActualChainForwardOrder
import Lamping.Lambda.NonterminalReadingDirections
import Lamping.Lamping.RedexChainDegrees
namespace Lamping.Lambda.Labelled
open SyntaxIncidence

/-- Internal endpoint geometry; no sort is added to bare incidence. -/
def ProperKind (t : LTerm) (v : ProperPosition t) (isApp : Bool) : Prop :=
  if isApp then ∃ stamp fn arg,t.subterm v.val=some (.app stamp fn arg)
  else ∃ stamp body,t.subterm v.val=some (.lam stamp body)

def departureApp : Step → Bool
  | .fn | .arg => true
  | .body => false

def targetApp : LTerm → Bool
  | .app _ _ _ => true
  | .var _ _ | .lam _ _ => false

theorem Source.actual_kind (actual : Source t edge (some v)) :
    ∃ step,edge.getLast?=some step ∧ProperKind t v (departureApp step) := by
  obtain ⟨step,child,port,split,lookup,departure⟩:=actual
  refine ⟨step,?_,?_⟩
  · rw [split];simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
  · cases departure with
    | fn => exact ⟨_,_,_,lookup⟩
    | arg => exact ⟨_,_,_,lookup⟩
    | body => exact ⟨_,_,lookup⟩

theorem Target.actual_kind (actual : Target t edge (some v)) (lookup : t.subterm edge=some node) :
    ProperKind t v (targetApp node) := by
  rcases actual with eq | ⟨stamp,index,origin,body,tail,atVar,atBinder,split,depth⟩
  · rw [eq] at lookup
    cases node with
    | app stamp fn arg => exact ⟨stamp,fn,arg,lookup⟩
    | lam stamp body => exact ⟨stamp,body,lookup⟩
    | var stamp index =>
      rcases v.property with ⟨a,fn,arg,atApp⟩ | ⟨a,body,atLambda⟩
      · rw [lookup] at atApp;cases atApp
      · rw [lookup] at atLambda;cases atLambda
  · have eq : node=.var stamp index := Option.some.inj (lookup.symm.trans atVar)
    rw [eq];exact ⟨origin,body,atBinder⟩

/-- SAME INIT/history label equality synchronizes the kind of both real
endpoints, including variable-to-lexical-binder targets. Not coordinate equality. -/
theorem History.equal_label_endpoint_kinds
    {ps : List Path} {source current left right : LTerm}
    {e f : Path} {a b c d : ProperPosition current}
    (labels : History ps source current) (initial : INIT source)
    (leftLookup : current.subterm e=some left) (rightLookup : current.subterm f=some right)
    (same : left.label=right.label)
    (leftSource : Source current e (some a)) (rightSource : Source current f (some b))
    (leftTarget : Target current e (some c)) (rightTarget : Target current f (some d)) :
    ∃ sourceKind targetKind,ProperKind current a sourceKind ∧ProperKind current b sourceKind ∧
      ProperKind current c targetKind ∧ProperKind current d targetKind := by
  obtain ⟨ls,lr,lk⟩:=Source.actual_kind leftSource
  obtain ⟨rs,rr,rk⟩:=Source.actual_kind rightSource
  have roles:=labels.incoming_role_eq_of_label initial leftLookup rightLookup same
  rw [lr,rr] at roles
  have steps:=Option.some.inj roles
  subst rs
  have tags:=labels.node_constructor_eq_of_label initial leftLookup rightLookup same
  have equal : targetApp left=targetApp right := by cases left <;> cases right <;> simp_all [LTerm.constructorTag,targetApp]
  refine ⟨departureApp ls,targetApp left,lk,rk,Target.actual_kind leftTarget leftLookup,?_⟩
  rw [equal];exact Target.actual_kind rightTarget rightLookup

/-- A finite actual reading walk. Binder jumps are compressed, without
adding an edge or choosing another occurrence with the same label. -/
inductive SignedProperWalk (t : LTerm) : ProperPosition t →List Path →List Bool →List (ProperPosition t) →Prop where
  | nil (p) : SignedProperWalk t p [] [] [p]
  | cons {a b edge edges signs vertices forward} :
      PrerequisiteReadsDirected t a.val edge forward →
      (if forward then Source t edge (some a) ∧Target t edge (some b)
       else Target t edge (some a) ∧Source t edge (some b)) →
      SignedProperWalk t b edges signs vertices →
      SignedProperWalk t a (edge::edges) (forward::signs) (a::vertices)

theorem SignedProperWalk.forget (walk : SignedProperWalk t p edges signs vertices) :
    ProperIncidenceWalk t p edges vertices := by
  induction walk with
  | nil => exact .nil _
  | @cons a b edge edges signs vertices forward reading step tail ih =>
    refine ProperIncidenceWalk.cons ?_ ih
    cases forward
    · exact Or.inr step
    · exact Or.inl step

private theorem source_parent_target (actual : Source t (parent++[step]) (some vertex)) :
    Target t parent (some vertex) := by
  obtain ⟨child,node,port,split,lookup,departure⟩:=actual
  have length:=congrArg List.length split
  simp only [List.length_append,List.length_singleton] at length
  have equal : parent=vertex.val := List.append_inj_left split (by omega)
  exact Or.inl equal

/-- Every actual successful chain supplies its finite reading signs and
proper walk. This statement adds no chosen orientation premise. -/
theorem PrerequisiteChain.signed_path (chain : PrerequisiteChain t start edges) :
    ∃ first signs vertices,Target t start (some first) ∧SignedProperWalk t first edges signs vertices := by
  induction chain with
  | @redex_app p a l body arg lookup =>
    let app : ProperPosition t := ⟨p,Or.inl ⟨a,_,arg,lookup⟩⟩
    have atLambda : t.subterm (p++[.fn])=some (.lam l body) := by rw [LTerm.subterm_append,lookup];rfl
    let lam : ProperPosition t := ⟨p++[.fn],Or.inr ⟨l,body,atLambda⟩⟩
    refine ⟨app,[true],[app,lam],Or.inl rfl,?_⟩
    exact .cons ⟨Or.inl ⟨a,.lam l body,arg,lookup,rfl⟩,rfl⟩
      ⟨⟨.fn,_,_,rfl,lookup,.fn⟩,Or.inl rfl⟩ (.nil _)
  | @redex_lam p a l body arg lookup =>
    let app : ProperPosition t := ⟨p,Or.inl ⟨a,_,arg,lookup⟩⟩
    have atLambda : t.subterm (p++[.fn])=some (.lam l body) := by rw [LTerm.subterm_append,lookup];rfl
    let lam : ProperPosition t := ⟨p++[.fn],Or.inr ⟨l,body,atLambda⟩⟩
    refine ⟨lam,[false],[lam,app],Or.inl rfl,?_⟩
    exact .cons ⟨Or.inr ⟨l,body,atLambda,rfl⟩,rfl⟩
      ⟨Or.inl rfl,⟨.fn,_,_,rfl,lookup,.fn⟩⟩ (.nil _)
  | @app p stamp fn arg edges lookup notLambda tail ih =>
    obtain ⟨first,signs,vertices,endpoint,walk⟩:=ih
    let app : ProperPosition t := ⟨p,Or.inl ⟨stamp,fn,arg,lookup⟩⟩
    refine ⟨app,true::signs,app::vertices,Or.inl rfl,?_⟩
    exact .cons ⟨Or.inl ⟨stamp,fn,arg,lookup,rfl⟩,rfl⟩
      ⟨⟨.fn,_,_,rfl,lookup,.fn⟩,endpoint⟩ walk
  | @lam parent child stamp body edges lookup notFunction tail ih =>
    obtain ⟨first,signs,vertices,endpoint,walk⟩:=ih
    have valid : (subtermAt t.erase (parent++[child])).isSome := by rw [←LTerm.erase_subterm,lookup];rfl
    obtain ⟨vertex,source⟩:=source_total t ⟨_,valid⟩
    cases vertex with
    | none => have length:=congrArg List.length source;simp at length
    | some vertex =>
      have eq : vertex=first := Option.some.inj (Target.unique (source_parent_target source) endpoint)
      subst vertex
      let lam : ProperPosition t := ⟨parent++[child],Or.inr ⟨stamp,body,lookup⟩⟩
      refine ⟨lam,false::signs,lam::vertices,Or.inl rfl,?_⟩
      exact .cons ⟨Or.inr ⟨stamp,body,lookup,rfl⟩,rfl⟩ ⟨Or.inl rfl,source⟩ walk
  | @var leaf stamp index parent origin body rest edges lookup binder split depth tail ih =>
    obtain ⟨first,signs,vertices,endpoint,walk⟩:=ih
    let lam : ProperPosition t := ⟨parent,Or.inr ⟨origin,body,binder⟩⟩
    have eq : first=lam := Option.some.inj (Target.unique endpoint (Or.inl rfl))
    subst first
    exact ⟨lam,signs,vertices,Or.inr ⟨stamp,index,origin,body,rest,lookup,binder,split,depth⟩,walk⟩

theorem ProperKind.unique (left : ProperKind t v kind) (right : ProperKind t v other) : kind=other := by
  cases kind <;> cases other
  · rfl
  · obtain ⟨a,body,atLambda⟩:=left
    obtain ⟨b,fn,arg,atApp⟩:=right
    rw [atLambda] at atApp;cases atApp
  · obtain ⟨a,fn,arg,atApp⟩:=left
    obtain ⟨b,body,atLambda⟩:=right
    rw [atApp] at atLambda;cases atLambda
  · rfl

theorem PrerequisiteReadsDirected.proper_kind
    {v : ProperPosition t} (reading : PrerequisiteReadsDirected t v.val edge forward) :
    ProperKind t v forward := by
  cases forward
  · rcases reading.1 with ⟨stamp,fn,arg,lookup,eq⟩ | ⟨stamp,body,lookup,eq⟩
    · have same:=eq.symm.trans reading.2
      have length:=congrArg List.length same;simp at length
    · exact ⟨stamp,body,lookup⟩
  · rcases reading.1 with ⟨stamp,fn,arg,lookup,eq⟩ | ⟨stamp,body,lookup,eq⟩
    · exact ⟨stamp,fn,arg,lookup⟩
    · have same:=eq.symm.trans reading.2
      have length:=congrArg List.length same;simp at length

private theorem read_lookup (reading : PrerequisiteReads t reader edge) :
    ∃node,t.subterm edge=some node := by
  rcases reading with ⟨a,fn,arg,lookup,eq⟩ | ⟨a,body,lookup,eq⟩
  · refine ⟨fn,?_⟩;rw [eq,LTerm.subterm_append,lookup];cases fn <;> rfl
  · exact ⟨_,eq ▸ lookup⟩

/-- Matching actual starting kinds synchronize the whole actual reading
walk. Label equality is used only through SAME generated-history provenance. -/
theorem SignedProperWalk.signs_eq
    {ps : List Path} {source current : LTerm} (labels : History ps source current) (initial : INIT source)
    {a b : ProperPosition current} {es fs : List Path} {ss ts : List Bool} {vs ws : List (ProperPosition current)}
    (left : SignedProperWalk current a es ss vs) (right : SignedProperWalk current b fs ts ws)
    (same : es.map current.labelAt=fs.map current.labelAt)
    (kind : ∃k,ProperKind current a k ∧ProperKind current b k) : ss=ts := by
  induction left generalizing b fs ts ws with
  | nil a =>
    cases right with
    | nil => rfl
    | cons => cases same
  | @cons a c edge edges signs vertices forward reading step tail ih =>
    cases right with
    | nil => cases same
    | @cons b d other rest more vertexes otherForward otherReading otherStep otherTail =>
      obtain ⟨k,ak,bk⟩:=kind
      have signEq : forward=otherForward :=
        (reading.proper_kind.unique ak).trans (otherReading.proper_kind.unique bk).symm
      obtain ⟨ln,ll⟩:=read_lookup reading.1
      obtain ⟨rn,rl⟩:=read_lookup otherReading.1
      have sameHead:= (List.cons.inj same).1
      have nodeEq : ln.label=rn.label := by simpa only [LTerm.labelAt,ll,rl,Option.map_some,Option.some.injEq] using sameHead
      have nextKind : ∃k,ProperKind current c k ∧ProperKind current d k := by
        cases forward <;> cases otherForward
        · obtain ⟨sk,tk,ak,bk,ck,dk⟩:=labels.equal_label_endpoint_kinds initial ll rl nodeEq step.2 otherStep.2 step.1 otherStep.1
          exact ⟨sk,ak,bk⟩
        · cases signEq
        · cases signEq
        · obtain ⟨sk,tk,ak,bk,ck,dk⟩:=labels.equal_label_endpoint_kinds initial ll rl nodeEq step.1 otherStep.1 step.2 otherStep.2
          exact ⟨tk,ck,dk⟩
      rw [signEq,ih otherTail (List.cons.inj same).2 nextKind]

private theorem head_not_redex (chain : PrerequisiteChain t start (edge::after))
    (nonempty : after≠[]) : ¬PrerequisiteRedexEdge t edge := by
  obtain ⟨before,last,split,redex,earlier⟩:=chain.redex_only_last
  cases before with
  | nil => simp only [List.nil_append,List.cons.injEq] at split;exact False.elim (nonempty split.2)
  | cons head tail => exact earlier edge (by rw [(List.cons.inj split).1];exact List.mem_cons_self)

theorem SignedProperWalk.signs_eq_of_multiedge
    {ps : List Path} {source current : LTerm}
    {leftStart rightStart : Path} {es fs : List Path} {a b : ProperPosition current}
    {ss ts : List Bool} {vs ws : List (ProperPosition current)} (labels : History ps source current) (initial : INIT source)
    (leftChain : PrerequisiteChain current leftStart es) (rightChain : PrerequisiteChain current rightStart fs)
    (left : SignedProperWalk current a es ss vs) (right : SignedProperWalk current b fs ts ws)
    (same : es.map current.labelAt=fs.map current.labelAt) (multi : 1<es.length) : ss=ts := by
  cases left with
  | nil => simp at multi
  | @cons a c edge edges signs vertices forward reading step tail =>
    cases right with
    | nil => cases same
    | @cons b d other rest more vertexes otherForward otherReading otherStep otherTail =>
      have length:=congrArg List.length same
      simp only [List.length_map,List.length_cons] at length multi
      have leftMore : edges≠[] := by intro eq;rw [eq] at multi;simp at multi
      have rightMore : rest≠[] := by intro eq;rw [eq] at length;simp only [List.length_nil] at length;omega
      obtain ⟨ln,ll⟩:=read_lookup reading.1
      obtain ⟨rn,rl⟩:=read_lookup otherReading.1
      have nodeEq : ln.label=rn.label := by
        have h:=(List.cons.inj same).1
        simpa only [LTerm.labelAt,ll,rl,Option.map_some,Option.some.injEq] using h
      have signEq:=labels.equal_label_nonredex_read_direction initial ll rl nodeEq reading otherReading
        (head_not_redex leftChain leftMore) (head_not_redex rightChain rightMore)
      apply SignedProperWalk.signs_eq labels initial (.cons reading step tail) (.cons otherReading otherStep otherTail) same
      exact ⟨forward,reading.proper_kind,signEq ▸ otherReading.proper_kind⟩

/-- A fixed first proper vertex and literal edge list determine the walk,
even before any generated-history or label hypothesis. -/
theorem ProperIncidenceWalk.vertices_unique
    (left : ProperIncidenceWalk t a edges vs) (right : ProperIncidenceWalk t a edges ws) : vs=ws := by
  induction left generalizing ws with
  | nil => cases right;rfl
  | @cons a b edge edges vertices step tail ih =>
    cases right with
    | @cons _ d _ _ more otherStep otherTail =>
      have eq : b=d := by
        rcases step with ⟨sa,tb⟩ | ⟨ta,sb⟩ <;> rcases otherStep with ⟨sc,td⟩ | ⟨tc,sd⟩
        · exact Option.some.inj (Target.unique tb td)
        · exact (Option.some.inj (Target.unique tb tc)).trans (Option.some.inj (Source.unique sa sd))
        · exact (Option.some.inj (Source.unique sb sc)).trans (Option.some.inj (Target.unique ta td))
        · exact Option.some.inj (Source.unique sb sd)
      subst d
      exact congrArg (List.cons a) (ih otherTail)

theorem SignedProperWalk.slot (walk : SignedProperWalk t first edges signs vertices)
    (k : Nat) (bound : k<edges.length) :
    ∃a b forward,vertices[k]?=some a ∧vertices[k+1]?=some b ∧signs[k]?=some forward ∧
      (if forward then Source t edges[k] (some a) ∧Target t edges[k] (some b)
       else Target t edges[k] (some a) ∧Source t edges[k] (some b)) := by
  induction walk generalizing k with
  | nil => simp at bound
  | @cons a b edge edges signs vertices forward reading step tail ih =>
    cases k with
    | zero =>
      have first : vertices[0]?=some b := by cases tail <;> rfl
      exact ⟨a,b,forward,rfl,by simpa only [List.getElem?_cons_succ,Nat.zero_add] using first,rfl,step⟩
    | succ k =>
      have small : k<edges.length := by simp only [List.length_cons] at bound;omega
      obtain ⟨c,d,f,cAt,dAt,sAt,actual⟩:=ih k small
      refine ⟨c,d,f,?_,?_,?_,?_⟩
      · simpa only [List.getElem?_cons_succ] using cAt
      · simpa only [List.getElem?_cons_succ,Nat.succ_eq_add_one,Nat.add_assoc] using dAt
      · simpa only [List.getElem?_cons_succ] using sAt
      · simpa only [List.getElem_cons_succ] using actual
end Lamping.Lambda.Labelled
namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence

def IndexedSimpleIncidencePath.OrientedAt (path : IndexedSimpleIncidencePath g n) (k : Fin n) (forward : Bool) : Prop :=
  if forward then g.source (path.edges k)=path.vertices ⟨k.val,by omega⟩ ∧
    g.target (path.edges k)=path.vertices ⟨k.val+1,by omega⟩
  else g.target (path.edges k)=path.vertices ⟨k.val,by omega⟩ ∧
    g.source (path.edges k)=path.vertices ⟨k.val+1,by omega⟩

/-- Matching complete actual path presentations with the same finite
orientation data yield a bare iso; neither start nor sort is added to it. -/
def IndexedSimpleIncidencePath.isoOfOrientations
    (left : IndexedSimpleIncidencePath g n) (right : IndexedSimpleIncidencePath h n)
    (orientations : ∀ k,∃f,left.OrientedAt k f ∧right.OrientedAt k f)
    (labels : ∀k,g.label (left.edges k)=h.label (right.edges k)) : ChainIncidenceIso g h where
  vertices := left.vertices.symm.trans right.vertices
  edges := left.edges.symm.trans right.edges
  source_eq := by
    intro e
    let k:=left.edges.invFun e
    have ee : left.edges k=e := left.edges.right_inv e
    obtain ⟨f,l,r⟩:=orientations k
    change right.vertices (left.vertices.invFun (g.source e))=h.source (right.edges k)
    rw [←ee]
    cases f
    · rw [show g.source (left.edges k)=left.vertices ⟨k.val+1,by omega⟩ from l.2,left.vertices.left_inv]
      exact r.2.symm
    · rw [show g.source (left.edges k)=left.vertices ⟨k.val,by omega⟩ from l.1,left.vertices.left_inv]
      exact r.1.symm
  target_eq := by
    intro e
    let k:=left.edges.invFun e
    have ee : left.edges k=e := left.edges.right_inv e
    obtain ⟨f,l,r⟩:=orientations k
    change right.vertices (left.vertices.invFun (g.target e))=h.target (right.edges k)
    rw [←ee]
    cases f
    · rw [show g.target (left.edges k)=left.vertices ⟨k.val,by omega⟩ from l.1,left.vertices.left_inv]
      exact r.1.symm
    · rw [show g.target (left.edges k)=left.vertices ⟨k.val+1,by omega⟩ from l.2,left.vertices.left_inv]
      exact r.2.symm
  label_eq := by
    intro e
    have h:=labels (left.edges.invFun e)
    rw [left.edges.right_inv] at h
    exact h

def IndexedSimpleIncidencePath.isoOfOrientationLength
    (size : n=m) (left : IndexedSimpleIncidencePath g n) (right : IndexedSimpleIncidencePath h m)
    (orientations : ∀k : Fin n,∃f,left.OrientedAt k f ∧right.OrientedAt ⟨k.val,by omega⟩ f)
    (labels : ∀k : Fin n,g.label (left.edges k)=h.label (right.edges ⟨k.val,by omega⟩)) : ChainIncidenceIso g h := by
  subst m
  exact left.isoOfOrientations right orientations labels

private theorem actual_vertex_slot
    {t : LTerm} {start : Path} {edges : List Path} {closed : Closed t.erase}
    {chain : PrerequisiteChain t start edges} {vertex : ProperPosition t}
    (actual : ActualChainPathPresentation closed chain) (k : Fin (edges.length+1))
    (atVertex : actual.vertices[k.val]?=some vertex) :
    (actual.presentation.vertices k).val=some vertex := by
  have bound : k.val<actual.vertices.length := by have length:=actual.walk.length;omega
  rw [List.getElem?_eq_getElem bound] at atVertex
  have eq : actual.vertices.get ⟨k.val,bound⟩=vertex := by
    simpa only [List.get_eq_getElem] using Option.some.inj atVertex
  exact (actual.vertex_at k).trans (congrArg some eq)

theorem ActualChainPathPresentation.signed_orientation
    {current : LTerm} {start : Path} {edges : List Path} {closed : Closed current.erase}
    {chain : PrerequisiteChain current start edges}
    (actual : ActualChainPathPresentation closed chain)
    (walk : SignedProperWalk current actual.first edges signs actual.vertices) (k : Fin edges.length) :
    ∃f,signs[k.val]?=some f ∧actual.presentation.OrientedAt k f := by
  obtain ⟨a,b,f,atA,atB,atF,step⟩:=walk.slot k.val k.isLt
  have leftAt:=actual_vertex_slot actual ⟨k.val,by omega⟩ atA
  have rightAt:=actual_vertex_slot actual ⟨k.val+1,by omega⟩ atB
  have fromA (source : Source current edges[k.val] (some a)) :
      (chainSyntaxIncidence current closed edges).source (actual.presentation.edges k)=actual.presentation.vertices ⟨k.val,by omega⟩ := by
    apply Subtype.ext
    change SyntaxIncidence.source current (actual.presentation.edges k).val=(actual.presentation.vertices ⟨k.val,by omega⟩).val
    have spec : Source current (actual.presentation.edges k).val.val (some a) := by rw [actual.edge_at];exact source
    exact (source_eq_of_spec current _ spec).trans leftAt.symm
  have fromB (source : Source current edges[k.val] (some b)) :
      (chainSyntaxIncidence current closed edges).source (actual.presentation.edges k)=actual.presentation.vertices ⟨k.val+1,by omega⟩ := by
    apply Subtype.ext
    change SyntaxIncidence.source current (actual.presentation.edges k).val=(actual.presentation.vertices ⟨k.val+1,by omega⟩).val
    have spec : Source current (actual.presentation.edges k).val.val (some b) := by rw [actual.edge_at];exact source
    exact (source_eq_of_spec current _ spec).trans rightAt.symm
  have toA (target : Target current edges[k.val] (some a)) :
      (chainSyntaxIncidence current closed edges).target (actual.presentation.edges k)=actual.presentation.vertices ⟨k.val,by omega⟩ := by
    apply Subtype.ext
    change SyntaxIncidence.target current closed (actual.presentation.edges k).val=(actual.presentation.vertices ⟨k.val,by omega⟩).val
    have spec : Target current (actual.presentation.edges k).val.val (some a) := by rw [actual.edge_at];exact target
    exact (target_eq_of_spec current closed _ spec).trans leftAt.symm
  have toB (target : Target current edges[k.val] (some b)) :
      (chainSyntaxIncidence current closed edges).target (actual.presentation.edges k)=actual.presentation.vertices ⟨k.val+1,by omega⟩ := by
    apply Subtype.ext
    change SyntaxIncidence.target current closed (actual.presentation.edges k).val=(actual.presentation.vertices ⟨k.val+1,by omega⟩).val
    have spec : Target current (actual.presentation.edges k).val.val (some b) := by rw [actual.edge_at];exact target
    exact (target_eq_of_spec current closed _ spec).trans rightAt.symm
  refine ⟨f,atF,?_⟩
  cases f
  · exact ⟨toA step.1,fromB step.2⟩
  · exact ⟨fromA step.1,toB step.2⟩

private theorem signed_at_actual_presentation
    {t : LTerm} {start : Path} {edges : List Path} {closed : Closed t.erase}
    {chain : PrerequisiteChain t start edges}
    (actual : ActualChainPathPresentation closed chain) :
    ∃signs,SignedProperWalk t actual.first edges signs actual.vertices := by
  obtain ⟨first,signs,vertices,endpoint,walk⟩:=chain.signed_path
  have eq : first=actual.first := Option.some.inj (Target.unique endpoint actual.endpoint)
  have aligned : SignedProperWalk t actual.first edges signs vertices := eq ▸ walk
  have verticesEq:=actual.walk.vertices_unique aligned.forget
  exact ⟨signs,verticesEq.symm ▸ aligned⟩

private theorem actual_edge_labelAt (t : LTerm) (edge : SyntaxIncidence.Edge t) :
    t.labelAt edge.val=some (SyntaxIncidence.label t edge) := by
  obtain ⟨node,lookup⟩:=SyntaxIncidence.edge_lookup t edge
  rw [LTerm.labelAt,lookup,Option.map_some,SyntaxIncidence.label_of_lookup t edge lookup]

private theorem equal_slot_labels
    {t : LTerm} {es fs : List Path} {start otherStart : Path} {closed : Closed t.erase}
    {left : PrerequisiteChain t start es} {right : PrerequisiteChain t otherStart fs}
    (first : ActualChainPathPresentation closed left) (second : ActualChainPathPresentation closed right)
    (same : es.map t.labelAt=fs.map t.labelAt) (length : es.length=fs.length) (k : Fin es.length) :
    (chainSyntaxIncidence t closed es).label (first.presentation.edges k)=
      (chainSyntaxIncidence t closed fs).label (second.presentation.edges ⟨k.val,by omega⟩) := by
  let j : Fin fs.length:=⟨k.val,by omega⟩
  have slots : t.labelAt (es.get k)=t.labelAt (fs.get j) := by
    have h:=congrArg (fun xs : List (Option Label)=>xs[k.val]?) same
    have rightBound : k.val<fs.length := j.isLt
    simpa only [List.getElem?_map,List.getElem?_eq_getElem k.isLt,List.getElem?_eq_getElem rightBound,
      Option.map_some,Option.some.injEq,List.get_eq_getElem] using h
  change SyntaxIncidence.label t (first.presentation.edges k).val=SyntaxIncidence.label t (second.presentation.edges j).val
  apply Option.some.inj
  rw [←actual_edge_labelAt,←actual_edge_labelAt,first.edge_at,second.edge_at]
  exact slots

theorem actual_multichain_iso_of_labels
    {ps : List Path} {source current : LTerm} {es fs : List Path} {leftStart rightStart : Path}
    (labels : History ps source current) (initial : INIT source) (closed : Closed current.erase)
    (left : PrerequisiteChain current leftStart es) (right : PrerequisiteChain current rightStart fs)
    (same : es.map current.labelAt=fs.map current.labelAt) (multi : 1<es.length) :
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs) := by
  have length : es.length=fs.length := by simpa only [List.length_map] using congrArg List.length same
  let first:=actual_chain_incidence_presentation closed left
  let second:=actual_chain_incidence_presentation closed right
  obtain ⟨ss,lwalk⟩:=signed_at_actual_presentation first
  obtain ⟨ts,rwalk⟩:=signed_at_actual_presentation second
  have signs:=lwalk.signs_eq_of_multiedge labels initial left right rwalk same multi
  apply Nonempty.intro (IndexedSimpleIncidencePath.isoOfOrientationLength length first.presentation second.presentation ?_ ?_)
  · intro k
    obtain ⟨f,atF,orF⟩:=first.signed_orientation lwalk k
    obtain ⟨g,atG,orG⟩:=second.signed_orientation rwalk ⟨k.val,by omega⟩
    have eq : f=g := Option.some.inj (atF.symm.trans (by simpa only [signs] using atG))
    exact ⟨f,orF,eq ▸ orG⟩
  · exact equal_slot_labels first second same length

/-- Converse on complete successful chains generated from the SAME initial
source. No orientation, start, slot, kind or desired iso is supplied. -/
theorem actual_chain_iso_of_labels
    {ps : List Path} {source current : LTerm} {es fs : List Path} {leftStart rightStart : Path}
    (labels : History ps source current) (initial : INIT source) (closed : Closed current.erase)
    (left : PrerequisiteChain current leftStart es) (right : PrerequisiteChain current rightStart fs)
    (same : es.map current.labelAt=fs.map current.labelAt) :
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs) := by
  by_cases multi : 1<es.length
  · exact actual_multichain_iso_of_labels labels initial closed left right same multi
  · have length : es.length=fs.length := by simpa only [List.length_map] using congrArg List.length same
    cases es with
    | nil => exact False.elim (left.nonempty rfl)
    | cons e rest =>
      have empty : rest=[] := by apply List.length_eq_zero_iff.mp;simp only [List.length_cons] at multi;omega
      subst rest
      cases fs with
      | nil => exact False.elim (right.nonempty rfl)
      | cons f more =>
        have empty : more=[] := by apply List.length_eq_zero_iff.mp;simp only [List.length_cons,List.length_nil] at length;omega
        subst more
        obtain ⟨le,lastL,lp,la,ll,lb,larg,splitL,atL⟩:=left.last_redex
        obtain ⟨re,lastR,rp,ra,rl,rb,rarg,splitR,atR⟩:=right.last_redex
        have leEq : le=e := Option.some.inj lastL.symm
        have reEq : re=f := Option.some.inj lastR.symm
        have ePath := leEq.symm.trans splitL
        have fPath := reEq.symm.trans splitR
        rw [ePath,fPath] at same ⊢
        apply (redex_chain_iso_iff_degree closed atL atR).mpr
        have childL : current.subterm (lp++[.fn])=some (.lam ll lb) := by rw [LTerm.subterm_append,atL];rfl
        have childR : current.subterm (rp++[.fn])=some (.lam rl rb) := by rw [LTerm.subterm_append,atR];rfl
        have eq : ll=rl := by simpa only [List.map_cons,List.map_nil,List.cons.injEq,and_true,LTerm.labelAt,childL,childR,Option.map_some,Option.some.injEq,LTerm.label] using same
        rw [LTerm.degreeAt,atL,LTerm.degreeAt,atR,eq];rfl

/-- Under SAME generated-history provenance the bare incidence condition is
exactly full forward READ-label equality for actual complete chains. -/
theorem actual_chain_iso_iff_labels
    {ps : List Path} {source current : LTerm} {es fs : List Path} {leftStart rightStart : Path}
    (labels : History ps source current) (initial : INIT source) (closed : Closed current.erase)
    (left : PrerequisiteChain current leftStart es) (right : PrerequisiteChain current rightStart fs) :
    ChainIncidenceIsomorphic (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs) ↔
      es.map current.labelAt=fs.map current.labelAt := by
  constructor
  · rintro ⟨iso⟩
    exact actual_chain_labels_forward labels initial closed left right iso
  · exact actual_chain_iso_of_labels labels initial closed left right
end Lamping.AG
