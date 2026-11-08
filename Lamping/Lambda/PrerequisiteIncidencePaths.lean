import Lamping.Lambda.PrerequisiteVertexRanks
namespace Lamping.Lambda.Labelled
open SyntaxIncidence

/-- One actual syntax edge, read in either of its actual incidence directions. -/
def ProperIncidenceStep (t : LTerm) (edge : Path) (a b : ProperPosition t) : Prop :=
  (Source t edge (some a) ∧Target t edge (some b)) ∨
  (Target t edge (some a) ∧Source t edge (some b))

/-- The vertex list includes both ends; variable-to-binder jumps add no edge. -/
inductive ProperIncidenceWalk (t : LTerm) : ProperPosition t →List Path →List (ProperPosition t) →Prop where
  | nil (p) : ProperIncidenceWalk t p [] [p]
  | cons {a b edge edges vertices} : ProperIncidenceStep t edge a b →
      ProperIncidenceWalk t b edges vertices →ProperIncidenceWalk t a (edge::edges) (a::vertices)

theorem ProperIncidenceWalk.length (walk : ProperIncidenceWalk t p edges vertices) :
    vertices.length=edges.length+1 := by
  induction walk with
  | nil => rfl
  | cons step tail ih => simp only [List.length_cons];omega

theorem ProperIncidenceWalk.start_mem (walk : ProperIncidenceWalk t p edges vertices) :
    p∈vertices := by
  cases walk with
  | nil => exact List.mem_singleton_self _
  | cons => exact List.mem_cons_self

/-- Every actually incident proper endpoint is on this literal walk. -/
theorem ProperIncidenceWalk.covers_incident
    (walk : ProperIncidenceWalk t p edges vertices) (edge : Path) (vertex : ProperPosition t)
    (member : edge∈edges)
    (endpoint : Source t edge (some vertex) ∨Target t edge (some vertex)) : vertex∈vertices := by
  induction walk with
  | nil => cases member
  | @cons a b head rest vs step tail ih =>
    rcases List.mem_cons.mp member with equal | below
    · subst edge
      rcases step with ⟨fromA,toB⟩ | ⟨toA,fromB⟩
      · rcases endpoint with source | target
        · have equal := Option.some.inj (Source.unique source fromA)
          exact equal ▸ List.mem_cons_self
        · have equal := Option.some.inj (Target.unique target toB)
          exact equal ▸ List.mem_cons_of_mem a tail.start_mem
      · rcases endpoint with source | target
        · have equal := Option.some.inj (Source.unique source fromB)
          exact equal ▸ List.mem_cons_of_mem a tail.start_mem
        · have equal := Option.some.inj (Target.unique target toA)
          exact equal ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem a (ih below)

private theorem parent_source (lookup : t.subterm (parent++[child])=some node) :
    ∃vertex : ProperPosition t,Source t (parent++[child]) (some vertex) ∧vertex.val=parent := by
  have valid : (subtermAt t.erase (parent++[child])).isSome := by rw [←LTerm.erase_subterm,lookup];rfl
  obtain ⟨vertex,spec⟩ := source_total t ⟨_,valid⟩
  cases vertex with
  | none => have lengths := congrArg List.length spec;simp at lengths
  | some vertex =>
    obtain ⟨step,sub,port,split,atParent,departure⟩ := spec
    have equal : vertex.val=parent := by
      have sizes := congrArg List.length split
      simp only [List.length_append,List.length_singleton] at sizes
      exact (List.append_inj_left split (by omega)).symm
    exact ⟨vertex,⟨step,sub,port,split,atParent,departure⟩,equal⟩

private theorem no_head_in_tail
    (head : PrerequisiteChain t p (edge::edges))
    (tail : PrerequisiteChain t q edges) : ¬PrerequisiteIncident t edges p := by
  intro incident
  obtain ⟨more,actual,_,bound⟩ := tail.incident_chain incident
  have equal := head.unique actual
  have sizes := congrArg List.length equal
  simp only [List.length_cons] at sizes
  omega

/-- A real successful chain is a simple proper-vertex incidence path. Its
actual starting vertex is the Target of the selected syntax occurrence. -/
theorem PrerequisiteChain.incidence_path (chain : PrerequisiteChain t start edges) :
    ∃first : ProperPosition t,∃vertices,
      Target t start (some first) ∧ProperIncidenceWalk t first edges vertices ∧
      vertices.Nodup ∧
      (∀vertex∈vertices,PrerequisiteIncident t edges vertex.val) := by
  induction chain with
  | @redex_app p a l body arg lookup =>
    let app : ProperPosition t := ⟨p,Or.inl ⟨a,_,arg,lookup⟩⟩
    have atLambda : t.subterm (p++[.fn])=some (.lam l body) := by rw [LTerm.subterm_append,lookup];rfl
    let lam : ProperPosition t := ⟨p++[.fn],Or.inr ⟨l,body,atLambda⟩⟩
    have fromApp : Source t (p++[.fn]) (some app) := ⟨.fn,_,_,rfl,lookup,.fn⟩
    have toLambda : Target t (p++[.fn]) (some lam) := Or.inl rfl
    have different : app≠lam := by
      intro equal
      have sizes := congrArg (fun v : ProperPosition t=>v.val.length) equal
      simp [app,lam] at sizes
    refine ⟨app,[app,lam],Or.inl rfl,.cons (Or.inl ⟨fromApp,toLambda⟩) (.nil _),by simp [different],?_⟩
    intro vertex member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨app.property,_,by simp,Or.inl fromApp⟩
    · have equal:=List.mem_singleton.mp member;subst vertex
      exact ⟨lam.property,_,by simp,Or.inr toLambda⟩
  | @redex_lam p a l body arg lookup =>
    let app : ProperPosition t := ⟨p,Or.inl ⟨a,_,arg,lookup⟩⟩
    have atLambda : t.subterm (p++[.fn])=some (.lam l body) := by rw [LTerm.subterm_append,lookup];rfl
    let lam : ProperPosition t := ⟨p++[.fn],Or.inr ⟨l,body,atLambda⟩⟩
    have fromApp : Source t (p++[.fn]) (some app) := ⟨.fn,_,_,rfl,lookup,.fn⟩
    have toLambda : Target t (p++[.fn]) (some lam) := Or.inl rfl
    have different : lam≠app := by
      intro equal
      have sizes := congrArg (fun v : ProperPosition t=>v.val.length) equal
      simp [app,lam] at sizes
    refine ⟨lam,[lam,app],toLambda,.cons (Or.inr ⟨toLambda,fromApp⟩) (.nil _),by simp [different],?_⟩
    intro vertex member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨lam.property,_,by simp,Or.inr toLambda⟩
    · have equal:=List.mem_singleton.mp member;subst vertex
      exact ⟨app.property,_,by simp,Or.inl fromApp⟩
  | @app p stamp fn arg es lookup notLambda tail ih =>
    obtain ⟨first,vertices,endpoint,walk,nodup,incident⟩ := ih
    let current : ProperPosition t := ⟨p,Or.inl ⟨stamp,fn,arg,lookup⟩⟩
    have source : Source t (p++[.fn]) (some current) := ⟨.fn,_,_,rfl,lookup,.fn⟩
    have absent : current∉vertices := by
      intro member
      exact no_head_in_tail (.app lookup notLambda tail) tail (incident current member)
    refine ⟨current,current::vertices,Or.inl rfl,.cons (Or.inl ⟨source,endpoint⟩) walk,
      List.nodup_cons.mpr ⟨absent,nodup⟩,?_⟩
    intro vertex member
    rcases List.mem_cons.mp member with rfl | below
    · exact ⟨current.property,_,List.mem_cons_self,Or.inl source⟩
    · obtain ⟨proper,edge,member,spec⟩ := incident vertex below
      exact ⟨proper,edge,List.mem_cons_of_mem _ member,spec⟩
  | @lam parent child stamp body es lookup notFunction tail ih =>
    obtain ⟨first,vertices,endpoint,walk,nodup,incident⟩ := ih
    obtain ⟨parentVertex,source,parentEq⟩ := parent_source lookup
    have parentTarget : Target t parent (some parentVertex) := Or.inl parentEq.symm
    have equal : first=parentVertex := Option.some.inj (Target.unique endpoint parentTarget)
    subst first
    let current : ProperPosition t := ⟨parent++[child],Or.inr ⟨stamp,body,lookup⟩⟩
    have currentTarget : Target t (parent++[child]) (some current) := Or.inl rfl
    have absent : current∉vertices := by
      intro member
      exact no_head_in_tail (.lam lookup notFunction tail) tail (incident current member)
    refine ⟨current,current::vertices,currentTarget,.cons (Or.inr ⟨currentTarget,source⟩) walk,
      List.nodup_cons.mpr ⟨absent,nodup⟩,?_⟩
    intro vertex member
    rcases List.mem_cons.mp member with rfl | below
    · exact ⟨current.property,_,List.mem_cons_self,Or.inr currentTarget⟩
    · obtain ⟨proper,edge,member,spec⟩ := incident vertex below
      exact ⟨proper,edge,List.mem_cons_of_mem _ member,spec⟩
  | @var leaf stamp index parent origin body rest es lookup binder split depth tail ih =>
    obtain ⟨first,vertices,endpoint,walk,nodup,incident⟩ := ih
    let parentVertex : ProperPosition t := ⟨parent,Or.inr ⟨origin,body,binder⟩⟩
    have parentTarget : Target t parent (some parentVertex) := Or.inl rfl
    have equal : first=parentVertex := Option.some.inj (Target.unique endpoint parentTarget)
    subst first
    exact ⟨parentVertex,vertices,Or.inr ⟨stamp,index,origin,body,rest,lookup,binder,split,depth⟩,
      walk,nodup,incident⟩
end Lamping.Lambda.Labelled
