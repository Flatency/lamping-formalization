import Lamping.Lamping.SimpleIncidencePathIso
import Lamping.Lambda.PrerequisiteIncidencePaths
import Lamping.Lamping.ChainSyntaxIncidence
namespace Lamping.AG
open Graph Lambda Lambda.Labelled SyntaxIncidence

private theorem list_get_injective {A : Type} {xs : List A} (nodup : xs.Nodup) :
    Function.Injective xs.get := by
  intro i j equal
  apply Fin.ext
  apply List.getElem?_inj i.isLt nodup
  simpa only [List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem j.isLt,List.get_eq_getElem] using congrArg some equal

private noncomputable def listSlots {A : Type} (xs : List A) (nodup : xs.Nodup) :
    Bij (Fin xs.length) {a : A //a∈xs} := by
  let toSlot (a : {a : A //a∈xs}) := Classical.choose (List.mem_iff_get.mp a.property)
  have chosen (a : {a : A //a∈xs}) : xs.get (toSlot a)=a.val := Classical.choose_spec (List.mem_iff_get.mp a.property)
  exact ⟨fun i=>⟨xs.get i,List.get_mem xs i⟩,toSlot,
    fun i=>list_get_injective nodup (chosen _),fun a=>Subtype.ext (chosen a)⟩

private theorem walk_edge_endpoints (walk : ProperIncidenceWalk t first edges vertices)
    (edge : Path) (member : edge∈edges) :
    ∃a b,a∈vertices ∧b∈vertices ∧ProperIncidenceStep t edge a b := by
  induction walk with
  | nil => cases member
  | @cons a b head rest vs step tail ih =>
    rcases List.mem_cons.mp member with equal | below
    · subst edge
      exact ⟨a,b,List.mem_cons_self,List.mem_cons_of_mem a tail.start_mem,step⟩
    · obtain ⟨x,y,xm,ym,actual⟩ := ih below
      exact ⟨x,y,List.mem_cons_of_mem a xm,List.mem_cons_of_mem a ym,actual⟩

private def selectedEdge (chain : PrerequisiteChain t start edges) (edge : Path)
    (member : edge∈edges) : Edge t := by
  refine ⟨edge,?_⟩
  rcases chain.eligible member with ⟨parent,stamp,fn,arg,equal,lookup⟩ | ⟨stamp,body,lookup⟩
  · rw [equal,←LTerm.erase_subterm,LTerm.subterm_append,lookup]
    cases fn <;> rfl
  · rw [←LTerm.erase_subterm,lookup];rfl

private theorem visited_incident
    {t : LTerm} (closed : Closed t.erase) (chain : PrerequisiteChain t start edges)
    (p : ProperPosition t) (incident : PrerequisiteIncident t edges p.val) :
    (syntaxIncidenceGraph t closed).Incident (fun e=>e.val∈edges) (some p) := by
  obtain ⟨proper,edge,member,spec⟩ := incident
  let actual := selectedEdge chain edge member
  refine ⟨actual,member,?_⟩
  rcases spec with source | target
  · exact Or.inl (source_eq_of_spec t actual source).symm
  · exact Or.inr (target_eq_of_spec t closed actual target).symm

private noncomputable def vertexMembers
    {t : LTerm} {start : Path} {edges : List Path}
    {first : ProperPosition t} {vertices : List (ProperPosition t)} (closed : Closed t.erase) (chain : PrerequisiteChain t start edges)
    (walk : ProperIncidenceWalk t first edges vertices)
    (incident : ∀(p : ProperPosition t),p∈vertices →PrerequisiteIncident t edges p.val) :
    Bij {p : ProperPosition t //p∈vertices} (chainSyntaxIncidence t closed edges).Vertex := by
  let forward (p : {p : ProperPosition t //p∈vertices}) : (chainSyntaxIncidence t closed edges).Vertex :=
    ⟨some p.val,visited_incident closed chain p.val (incident p.val p.property)⟩
  have covered (v : (chainSyntaxIncidence t closed edges).Vertex) :
      ∃p : {p : ProperPosition t //p∈vertices},v.val=some p.val := by
    obtain ⟨edge,member,endpoint⟩ := v.property
    obtain ⟨a,b,am,bm,step⟩ := walk_edge_endpoints walk edge.val member
    rcases step with ⟨sa,tb⟩ | ⟨ta,sb⟩
    · rcases endpoint with sourceSide | targetSide
      · exact ⟨⟨a,am⟩,sourceSide.trans (source_eq_of_spec t edge sa)⟩
      · exact ⟨⟨b,bm⟩,targetSide.trans (target_eq_of_spec t closed edge tb)⟩
    · rcases endpoint with sourceSide | targetSide
      · exact ⟨⟨b,bm⟩,sourceSide.trans (source_eq_of_spec t edge sb)⟩
      · exact ⟨⟨a,am⟩,targetSide.trans (target_eq_of_spec t closed edge ta)⟩
  let backward (v : (chainSyntaxIncidence t closed edges).Vertex) := Classical.choose (covered v)
  have chosen (v : (chainSyntaxIncidence t closed edges).Vertex) : v.val=some (backward v).val :=
    Classical.choose_spec (covered v)
  refine ⟨forward,backward,?_,?_⟩
  · intro p
    apply Subtype.ext
    exact (Option.some.inj (chosen (forward p))).symm
  · intro v
    exact Subtype.ext (chosen v).symm

private def edgeMembers (chain : PrerequisiteChain t start edges) :
    Bij {p : Path //p∈edges} (chainSyntaxIncidence t closed edges).Edge where
  toFun p := ⟨selectedEdge chain p.val p.property,p.property⟩
  invFun edge := ⟨edge.val.val,edge.property⟩
  left_inv p := rfl
  right_inv edge := by apply Subtype.ext;exact Subtype.ext rfl

private theorem walk_first_get (walk : ProperIncidenceWalk t first edges vertices) :
    vertices.get ⟨0,by have length:=walk.length;omega⟩=first := by cases walk <;> rfl

private theorem walk_at_index (walk : ProperIncidenceWalk t first edges vertices)
    (k : Fin edges.length) :
    ProperIncidenceStep t (edges.get k)
      (vertices.get ⟨k.val,by have length:=walk.length;omega⟩)
      (vertices.get ⟨k.val+1,by have length:=walk.length;omega⟩) := by
  induction walk with
  | nil => exact False.elim (Nat.not_lt_zero _ k.isLt)
  | @cons a b edge rest vs step tail ih =>
    rcases k with ⟨index,bound⟩
    cases index with
    | zero =>
      have first:=walk_first_get tail
      simpa only [List.get_cons_zero,List.get_cons_succ,first] using step
    | succ index =>
      have limit : index<rest.length := by simp only [List.length_cons] at bound;omega
      simpa only [List.get_cons_succ,Nat.succ_eq_add_one] using ih ⟨index,limit⟩

/-- The actual proper walk is retained alongside its induced finite
incidence presentation. Enumeration follows the literal lists, not labels. -/
structure ActualChainPathPresentation {t : LTerm} {start : Path} {edges : List Path}
    (closed : Closed t.erase) (chain : PrerequisiteChain t start edges) where
  first : ProperPosition t
  vertices : List (ProperPosition t)
  endpoint : Target t start (some first)
  walk : ProperIncidenceWalk t first edges vertices
  nodup : vertices.Nodup
  presentation : IndexedSimpleIncidencePath (chainSyntaxIncidence t closed edges) edges.length
  vertex_at : ∀k,(presentation.vertices k).val=some (vertices.get ⟨k.val,by have length:=walk.length;omega⟩)
  edge_at : ∀k,(presentation.edges k).val.val=edges.get k

theorem ActualChainPathPresentation.vertex_zero
    (actual : ActualChainPathPresentation closed chain) :
    (actual.presentation.vertices 0).val=some actual.first := by
  have first : actual.vertices.get ⟨0,by have length:=actual.walk.length;omega⟩=actual.first := by
    exact walk_first_get actual.walk
  exact (actual.vertex_at 0).trans (congrArg some first)

noncomputable def actual_chain_incidence_presentation
    {t : LTerm} (closed : Closed t.erase) (chain : PrerequisiteChain t start edges) :
    ActualChainPathPresentation closed chain := by
  classical
  apply Classical.choice
  obtain ⟨first,vertices,endpoint,walk,nodup,incident⟩ := chain.incidence_path
  have length := walk.length
  let reindex : Bij (Fin (edges.length+1)) (Fin vertices.length) :=
    ⟨fun k=>⟨k.val,by omega⟩,fun k=>⟨k.val,by omega⟩,fun _=>rfl,fun _=>rfl⟩
  let vertexEnum := reindex.trans ((listSlots vertices nodup).trans (vertexMembers closed chain walk incident))
  let edgeEnum := (listSlots edges chain.nodup).trans (edgeMembers (closed:=closed) chain)
  refine ⟨⟨first,vertices,endpoint,walk,nodup,⟨vertexEnum,edgeEnum,?_⟩,fun _=>rfl,fun _=>rfl⟩⟩
  intro k
  have actual := walk_at_index walk k
  rcases actual with ⟨source,target⟩ | ⟨target,source⟩
  · exact Or.inl ⟨Subtype.ext (source_eq_of_spec t _ source),Subtype.ext (target_eq_of_spec t closed _ target)⟩
  · exact Or.inr ⟨Subtype.ext (target_eq_of_spec t closed _ target),Subtype.ext (source_eq_of_spec t _ source)⟩
end Lamping.AG
