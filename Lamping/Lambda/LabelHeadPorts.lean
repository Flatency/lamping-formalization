import Lamping.Lambda.LabelFirstRedex
namespace Lamping.Lambda.Labelled

/-- Actual original application nodes paired with their function-root edge.
Keys are node labels, not current compound edge labels. -/
def appFunctionEdges (env : List Label) : LTerm → List (Label × SourceEdge)
  | .var _ _ => []
  | .lam l b => appFunctionEdges (l::env) b
  | .app l f a => (l,sourceEdge env (.appFn l) f)::(appFunctionEdges env f++appFunctionEdges env a)

theorem appFunctionEdges_keys (t : LTerm) (env) :
    ∀ l∈(appFunctionEdges env t).map Prod.fst,l∈t.labels := by
  induction t generalizing env with
  | var => simp [appFunctionEdges]
  | lam l b ih => exact fun a member => List.mem_cons_of_mem _ (ih _ a member)
  | app l f a hf ha =>
    intro key member
    simp only [appFunctionEdges,List.map_cons,List.map_append,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (hf _ key member))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ha _ key member))

theorem appFunctionEdges_keys_nodup (t : LTerm) (distinct : t.labels.Nodup) (env) :
    ((appFunctionEdges env t).map Prod.fst).Nodup := by
  induction t generalizing env with
  | var => exact List.nodup_nil
  | lam l b ih => exact ih (List.nodup_cons.mp distinct).2 _
  | app l f a hf ha =>
    obtain ⟨fresh,children⟩ := List.nodup_cons.mp distinct
    obtain ⟨fnDistinct,argDistinct,apart⟩ := List.nodup_append.mp children
    simp only [appFunctionEdges,List.map_cons,List.map_append]
    apply List.nodup_cons.mpr
    constructor
    · intro member
      rcases List.mem_append.mp member with member | member
      · exact fresh (List.mem_append_left _ (appFunctionEdges_keys f env l member))
      · exact fresh (List.mem_append_right _ (appFunctionEdges_keys a env l member))
    · apply List.nodup_append.mpr
      exact ⟨hf fnDistinct _,ha argDistinct _,fun x hx y hy eq =>
        apart x (appFunctionEdges_keys f env x hx) y (appFunctionEdges_keys a env y hy) eq⟩

private theorem pair_key_unique (entries : List (Label × SourceEdge))
    (distinct : (entries.map Prod.fst).Nodup) (one : (key,e)∈entries) (two : (key,f)∈entries) : e=f := by
  induction entries with
  | nil => cases one
  | cons head tail ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp distinct
    simp only [List.mem_cons] at one two
    rcases one with equal | one
    · cases equal
      rcases two with equal | two
      · exact (Prod.mk.inj equal).2.symm
      · exact False.elim (fresh (List.mem_map.mpr ⟨_,two,rfl⟩))
    · rcases two with equal | two
      · cases equal
        exact False.elim (fresh (List.mem_map.mpr ⟨_,one,rfl⟩))
      · exact ih rest one two

/-- A function port is either the current subtree's incoming boundary or the
unique function edge of an actual application node inside it. -/
theorem sourceEdges_function_port (t : LTerm) (member : e∈sourceEdges env ctx t)
    (start : e.fromPort=.appFn origin) :
    (ctx=.appFn origin ∧ e=sourceEdge env ctx t) ∨ (origin,e)∈appFunctionEdges env t := by
  induction t generalizing env ctx with
  | var l i =>
    simp only [sourceEdges,List.mem_singleton] at member
    cases member
    exact .inl ⟨start,rfl⟩
  | lam l b ih =>
    simp only [sourceEdges,List.mem_cons] at member
    rcases member with rfl | member
    · exact .inl ⟨start,rfl⟩
    · rcases ih member with ⟨wrong,_⟩ | inside
      · cases wrong
      · exact .inr inside
  | app l f a hf ha =>
    simp only [sourceEdges,List.mem_cons,List.mem_append] at member
    rcases member with rfl | member | member
    · exact .inl ⟨start,rfl⟩
    · rcases hf member with ⟨boundary,equal⟩ | inside
      · have same := SourcePort.appFn.inj boundary
        cases same
        cases equal
        exact .inr List.mem_cons_self
      · exact .inr (List.mem_cons_of_mem _ (List.mem_append_left _ inside))
    · rcases ha member with ⟨wrong,_⟩ | inside
      · cases wrong
      · exact .inr (List.mem_cons_of_mem _ (List.mem_append_right _ inside))

theorem SourceSubterm.appFunctionEdges_subset
    (atSite : SourceSubterm env ctx t p innerEnv innerCtx sub) :
    ∀ pair∈appFunctionEdges innerEnv sub,pair∈appFunctionEdges env t := by
  induction atSite with
  | nil => exact fun _ h => h
  | body _ ih => exact ih
  | fn _ ih => exact fun pair h => List.mem_cons_of_mem _ (List.mem_append_left _ (ih pair h))
  | arg _ ih => exact fun pair h => List.mem_cons_of_mem _ (List.mem_append_right _ (ih pair h))

/-- At a real initial redex, no other edge can emerge from the head function
port. The node identity uniqueness is derived from actual INIT syntax. -/
theorem SourceSubterm.head_function_edge_unique {body argument : LTerm}
    (atHead : SourceSubterm [] .external t p env ctx (.app beta (.lam alpha body) argument))
    (initial : INIT t) (member : e∈sourceEdges [] .external t)
    (start : e.fromPort=.appFn beta) :
    e=⟨alpha,.appFn beta,.lamContext alpha⟩ := by
  rcases sourceEdges_function_port t member start with ⟨wrong,_⟩ | actual
  · cases wrong
  · have headMember : (beta,⟨alpha,.appFn beta,.lamContext alpha⟩)∈appFunctionEdges [] t :=
      atHead.appFunctionEdges_subset _ List.mem_cons_self
    exact pair_key_unique _ (appFunctionEdges_keys_nodup t initial.2 []) actual headMember

theorem SourceRoute.head_function_support {body argument : LTerm}
    (atHead : SourceSubterm [] .external t p env ctx (.app beta (.lam alpha body) argument))
    (initial : INIT t)
    (route : SourceRoute (sourceEdges [] .external t) (.appFn beta) l finish)
    (support : l.Supported region) : alpha.Supported region := by
  obtain ⟨n,e,first,member,atomic,start⟩ := route.first_atom
  have same := atHead.head_function_edge_unique initial member start
  have equal : alpha=Label.atom n := by simpa only [same] using atomic
  rw [equal]
  exact Label.Supported.firstAtom support first

theorem SourceRoute.lambda_endpoint_support
    (route : SourceRoute (sourceEdges env ctx t) start l (.lamContext alpha))
    (support : l.Supported region) : alpha.Supported region := by
  obtain ⟨n,last,equal⟩ := route.lam_last_atom
  rw [equal]
  exact Label.Supported.lastAtom support last

/-- A genuine generated route whose recursive over/under turns avoid two
specified original nodes. Atomic edges remain the actual original edges. -/
inductive HeadFreeRoute (edges : List SourceEdge) (blockedApp blockedLam : Label) :
    SourcePort → Label → SourcePort → Prop where
  | atom (member : e∈edges) (atomic : e.atom=Label.atom n) :
      HeadFreeRoute edges blockedApp blockedLam e.fromPort (Label.atom n) e.toPort
  | over : appId≠blockedApp → lamId≠blockedLam →
      HeadFreeRoute edges blockedApp blockedLam start a (.appContext appId) →
      HeadFreeRoute edges blockedApp blockedLam (.appFn appId) degree (.lamContext lamId) →
      HeadFreeRoute edges blockedApp blockedLam (.lamBody lamId) b finish →
      HeadFreeRoute edges blockedApp blockedLam start ((a.concat degree.over).concat b) finish
  | under : appId≠blockedApp → lamId≠blockedLam →
      HeadFreeRoute edges blockedApp blockedLam start a (.lamBind lamId) →
      HeadFreeRoute edges blockedApp blockedLam (.appFn appId) degree (.lamContext lamId) →
      HeadFreeRoute edges blockedApp blockedLam (.appArg appId) b finish →
      HeadFreeRoute edges blockedApp blockedLam start ((a.concat degree.under).concat b) finish

theorem HeadFreeRoute.route (free : HeadFreeRoute edges blockedApp blockedLam start l finish) :
    SourceRoute edges start l finish := by
  induction free with
  | atom member atomic => exact .atom member atomic
  | over _ _ _ _ _ ha hd hb => exact .over ha hd hb
  | under _ _ _ _ _ ha hd hb => exact .under ha hd hb

/-- Avoiding the actual head lambda degree excludes every crossing of the
head's application/lambda turns, including recursively nested under routes. -/
theorem SourceRoute.head_free {body argument : LTerm}
    (atHead : SourceSubterm [] .external t p env ctx (.app beta (.lam alpha body) argument))
    (initial : INIT t) (outside : ¬alpha.Supported region)
    (route : SourceRoute (sourceEdges [] .external t) start l finish)
    (support : l.Supported region) :
    HeadFreeRoute (sourceEdges [] .external t) beta alpha start l finish := by
  induction route with
  | atom member atomic => exact .atom member atomic
  | @over start a appId degree lamId b finish left middle right hl hm hr =>
    obtain ⟨prefixSupport,suffix⟩ := (Label.supported_concat _ _ _).mp support
    obtain ⟨leftSupport,degreeSupport⟩ := (Label.supported_concat _ _ _).mp prefixSupport
    have appDifferent : appId≠beta := by
      intro equal
      cases equal
      exact outside (middle.head_function_support atHead initial degreeSupport)
    have lamDifferent : lamId≠alpha := by
      intro equal
      cases equal
      exact outside (middle.lambda_endpoint_support degreeSupport)
    exact .over appDifferent lamDifferent (hl leftSupport) (hm degreeSupport) (hr suffix)
  | @under start a lamId appId degree b finish left middle right hl hm hr =>
    obtain ⟨prefixSupport,suffix⟩ := (Label.supported_concat _ _ _).mp support
    obtain ⟨leftSupport,degreeSupport⟩ := (Label.supported_concat _ _ _).mp prefixSupport
    have appDifferent : appId≠beta := by
      intro equal
      cases equal
      exact outside (middle.head_function_support atHead initial degreeSupport)
    have lamDifferent : lamId≠alpha := by
      intro equal
      cases equal
      exact outside (middle.lambda_endpoint_support degreeSupport)
    exact .under appDifferent lamDifferent (hl leftSupport) (hm degreeSupport) (hr suffix)

/-- The cut statement for an actual transported redex degree. Both endpoint
nodes and every recursive over/under crossing avoid the original head nodes. -/
theorem History.generated_head_free_degree {body argument : LTerm}
    (history : History ps t u) (initial : INIT t)
    (atHead : SourceSubterm [] .external t p env ctx (.app beta (.lam alpha body) argument))
    (outside : ¬alpha.Supported region) (degree : u.degreeAt q=some l)
    (support : l.Supported region) :
    ∃ appId lamId,appId≠beta ∧ lamId≠alpha ∧
      HeadFreeRoute (sourceEdges [] .external t) beta alpha (.appFn appId) l (.lamContext lamId) := by
  obtain ⟨appId,lamId,route⟩ := (history.generated_source_routes initial).degree_route degree
  refine ⟨appId,lamId,?_,?_,route.head_free atHead initial outside support⟩
  · intro equal
    cases equal
    exact outside (route.head_function_support atHead initial support)
  · intro equal
    cases equal
    exact outside (route.lambda_endpoint_support support)
end Lamping.Lambda.Labelled

