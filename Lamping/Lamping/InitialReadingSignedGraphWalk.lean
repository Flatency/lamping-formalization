import Lamping.Lamping.ChainRepresentation
import Lamping.Lambda.PrerequisiteIncidencePaths
import Lamping.Lambda.LabelBetaCopyCover

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

private theorem valid_member (chain : PrerequisiteChain t p edges) (h : e ∈ edges) :
    (subtermAt t.erase e).isSome := by
  rcases chain.eligible h with ⟨parent,a,fn,arg,rfl,lookup⟩ | ⟨a,body,lookup⟩
  · have atFn : t.subterm (parent++[.fn])=some fn := by
      rw [LTerm.subterm_append,lookup]; cases fn <;> rfl
    rw [←LTerm.erase_subterm,atFn]; rfl
  · rw [←LTerm.erase_subterm,lookup]; rfl

private def positions (chain : PrerequisiteChain t p edges) : List (Position t.erase) :=
  edges.attach.map (fun e => ⟨e.val,valid_member chain e.property⟩)

private theorem positions_values (chain : PrerequisiteChain t p edges) :
    (positions chain).map (fun e => e.val)=edges := by
  simp [positions,List.map_map]

private theorem positions_cons (chain : PrerequisiteChain t p (e::es))
    (tail : PrerequisiteChain t q es) :
    positions chain=⟨e,valid_member chain (List.mem_cons_self)⟩::positions tail := by
  simp [positions,List.attach_cons,List.map_map]

private theorem positions_single (chain : PrerequisiteChain t p [e]) :
    positions chain=[⟨e,valid_member chain (by simp)⟩] := by simp [positions]

private def Starts (t : LTerm) (p : Path) (a : SourcePort) : Prop :=
  ∃ first : SyntaxIncidence.ProperPosition t,
    SyntaxIncidence.Target t p (some first) ∧
    ((∃ stamp fn arg,t.subterm first.val=some (.app stamp fn arg) ∧ a=.appFn stamp) ∨
      (∃ stamp body,t.subterm first.val=some (.lam stamp body) ∧ a=.lamContext stamp))

private theorem starts_app (lookup : t.subterm p=some (.app stamp fn arg))
    (h : Starts t p a) : a=.appFn stamp := by
  obtain ⟨v,target,kind⟩ := h
  let here : SyntaxIncidence.ProperPosition t := ⟨p,Or.inl ⟨stamp,fn,arg,lookup⟩⟩
  have same := Option.some.inj (SyntaxIncidence.Target.unique target
    (show SyntaxIncidence.Target t p (some here) from Or.inl rfl))
  subst v
  rcases kind with ⟨s,f,r,actual,port⟩ | ⟨s,b,actual,port⟩
  · have eq := LTerm.app.inj (Option.some.inj (lookup.symm.trans actual))
    exact port.trans (congrArg SourcePort.appFn eq.1.symm)
  · rw [lookup] at actual; cases actual

private theorem starts_lam (lookup : t.subterm p=some (.lam stamp body))
    (h : Starts t p a) : a=.lamContext stamp := by
  obtain ⟨v,target,kind⟩ := h
  let here : SyntaxIncidence.ProperPosition t := ⟨p,Or.inr ⟨stamp,body,lookup⟩⟩
  have same := Option.some.inj (SyntaxIncidence.Target.unique target
    (show SyntaxIncidence.Target t p (some here) from Or.inl rfl))
  subst v
  rcases kind with ⟨s,f,r,actual,port⟩ | ⟨s,b,actual,port⟩
  · rw [lookup] at actual; cases actual
  · have eq := LTerm.lam.inj (Option.some.inj (lookup.symm.trans actual))
    exact port.trans (congrArg SourcePort.lamContext eq.1.symm)

private theorem starts_app_intro (lookup : t.subterm p=some (.app stamp fn arg)) :
    Starts t p (.appFn stamp) :=
  ⟨⟨p,Or.inl ⟨stamp,fn,arg,lookup⟩⟩,Or.inl rfl,Or.inl ⟨stamp,fn,arg,lookup,rfl⟩⟩

private theorem starts_lam_intro (lookup : t.subterm p=some (.lam stamp body)) :
    Starts t p (.lamContext stamp) :=
  ⟨⟨p,Or.inr ⟨stamp,body,lookup⟩⟩,Or.inl rfl,Or.inr ⟨stamp,body,lookup,rfl⟩⟩

private theorem binder_port
    (occ : SourceSubterm [] .external t leaf env ctx (.var stamp index))
    (binder : t.subterm parent=some (.lam origin body))
    (split : leaf=parent++(.body::rest)) (depth : index=binderDepth rest) :
    sourceBinder env index=.lamBind origin := by
  have sizes := occ.env_length
  have counts := binderDepth_append parent (.body::rest)
  have pathCounts := congrArg binderDepth split
  have bound : index<env.length := by
    simp only [List.length_nil,Nat.zero_add] at sizes
    simp only [binderDepth] at counts
    omega
  cases entry : env[index]? with
  | none => have outside := List.getElem?_eq_none_iff.mp entry; omega
  | some actual =>
    obtain ⟨other,tail,inside,samePath,atOther,atDepth⟩ := occ.bound_binder_occurrence entry
    have same := binding_prefix_depth_unique (split.symm.trans samePath) (depth.symm.trans atDepth)
    rw [same.1] at binder
    have labels := (LTerm.lam.inj (Option.some.inj (binder.symm.trans atOther))).1
    simp only [sourceBinder,entry]
    exact congrArg SourcePort.lamBind labels.symm

private theorem variable_turn
    (occ : SourceSubterm [] .external t p env ctx (.var stamp index))
    (h : Starts t p a) : GraphTurn (sourceBinder env index) a := by
  obtain ⟨v,target,kind⟩ := h
  rcases target with atProper | ⟨s,i,origin,body,rest,atVar,atBinder,split,depth⟩
  · rcases v.property with ⟨s,f,r,actual⟩ | ⟨s,b,actual⟩ <;>
      rw [←atProper,occ.lookup] at actual <;> cases actual
  · have sameVar := LTerm.var.inj (Option.some.inj (occ.lookup.symm.trans atVar))
    have bound := binder_port occ atBinder split (sameVar.2.trans depth)
    rw [bound]
    rcases kind with ⟨s,f,r,actual,port⟩ | ⟨s,b,actual,port⟩
    · rw [atBinder] at actual; cases actual
    · have same := (LTerm.lam.inj (Option.some.inj (atBinder.symm.trans actual))).1
      rw [port,←same]
      exact .symm (.lamContextBind _)

private theorem source_member (occ : SourceSubterm [] .external t p env ctx node) :
    sourceEdge env ctx node∈sourceEdges [] .external t := by
  apply occ.edges_subset
  cases node <;> exact List.mem_cons_self

private theorem append_occ
    (outer : SourceSubterm env ctx t p innerEnv innerCtx sub)
    (inner : SourceSubterm innerEnv innerCtx sub q finalEnv finalCtx node) :
    SourceSubterm env ctx t (p++q) finalEnv finalCtx node := by
  induction outer generalizing q finalEnv finalCtx node with
  | nil => exact inner
  | fn _ ih => exact .fn (ih inner)
  | arg _ ih => exact .arg (ih inner)
  | body _ ih => exact .body (ih inner)

private theorem edge_forward (initial : INIT t)
    (occ : SourceSubterm [] .external t p env ctx node) :
    GraphWalk (sourceEdges [] .external t) ctx node.label.edgeWord
      (sourceEdge env ctx node).toPort := by
  obtain ⟨n,atomic⟩ := sourceEdges_atomic initial (source_member occ)
  have label : node.label=Label.atom n := by cases node <;> exact atomic
  have walk := GraphWalk.edge (SourceTraverse.forward (source_member occ) atomic)
  have fromPort : (sourceEdge env ctx node).fromPort=ctx := by cases node <;> rfl
  have word : node.label.edgeWord=[⟨n,false⟩] := by rw [label];rfl
  simpa only [fromPort,←word] using walk

private theorem selected_label
    {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {root : B}
    (selection : OccurrenceFragmentSelection t g root) (e : Position t.erase)
    (lookup : t.subterm e.val=some node) : (selection e).term.label=node.label := by
  have same := Option.some.inj ((selection e).occurrence.lookup.symm.trans lookup)
  exact congrArg LTerm.label same

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {t : LTerm} {g : Net signature N B W} {root : B}

private def signed (selection : OccurrenceFragmentSelection t g root)
    (chain : PrerequisiteChain t p es) (ds : List Bool) : EdgeWord :=
  (List.zipWith (fun position forward => if forward then (selection position).term.label.edgeWord
    else EdgeWord.reverse (selection position).term.label.edgeWord) (positions chain) ds).flatten

private theorem signed_walk (initial : INIT t)
    (selection : OccurrenceFragmentSelection t g root)
    (reading : PrerequisiteReading t p es ds) :
    ∃ a b,Starts t p a ∧ GraphWalk (sourceEdges [] .external t) a
      (signed selection reading.chain ds) b := by
  induction reading with
  | @redex_app p a l body arg lookup =>
    have atChild : t.subterm (p++[.fn])=some (.lam l body) := by rw [LTerm.subterm_append,lookup];rfl
    obtain ⟨env,ctx,occ⟩ := SourceSubterm.of_lookup t lookup [] .external
    have atFn : SourceSubterm [] .external t (p++[.fn]) env (.appFn a) (.lam l body) := append_occ occ (.fn .nil)
    refine ⟨.appFn a,.lamContext l,starts_app_intro lookup,?_⟩
    have word := edge_forward initial atFn
    simp only [signed,positions_single,List.zipWith_cons_cons,List.zipWith_nil_left,List.flatten_cons,
      List.flatten_nil,List.append_nil,if_true]
    rw [selected_label selection _ atChild]
    exact word
  | @redex_lam p a l body arg lookup =>
    have atChild : t.subterm (p++[.fn])=some (.lam l body) := by rw [LTerm.subterm_append,lookup];rfl
    obtain ⟨env,ctx,occ⟩ := SourceSubterm.of_lookup t lookup [] .external
    have atFn : SourceSubterm [] .external t (p++[.fn]) env (.appFn a) (.lam l body) := append_occ occ (.fn .nil)
    refine ⟨.lamContext l,.appFn a,starts_lam_intro atChild,?_⟩
    have word := (edge_forward initial atFn).reverse
    simp only [signed,positions_single,List.zipWith_cons_cons,List.zipWith_nil_left,List.flatten_cons,
      List.flatten_nil,List.append_nil,Bool.false_eq_true,if_false]
    rw [selected_label selection _ atChild]
    exact word
  | @app p a fn arg es ds lookup notLambda tail ih =>
    obtain ⟨left,right,start,walk⟩ := ih
    obtain ⟨env,ctx,occ⟩ := SourceSubterm.of_lookup t lookup [] .external
    have atFn : SourceSubterm [] .external t (p++[.fn]) env (.appFn a) fn := append_occ occ (.fn .nil)
    have turn : GraphTurn (sourceEdge env (.appFn a) fn).toPort left := by
      cases fn with
      | lam l b => exact False.elim (notLambda l b rfl)
      | app s f r => rw [starts_app atFn.lookup start]; exact .appContextFn _
      | var s i => exact variable_turn atFn start
    refine ⟨.appFn a,right,starts_app_intro lookup,?_⟩
    have both := GraphWalk.join (edge_forward initial atFn) turn walk
    simp only [signed,positions_cons _ tail.chain,List.zipWith_cons_cons,List.flatten_cons,if_true]
    rw [selected_label selection _ atFn.lookup]
    exact both
  | @lam parent step stamp body es ds lookup notFunction tail ih =>
    obtain ⟨left,right,start,walk⟩ := ih
    obtain ⟨env,ctx,occ⟩ := SourceSubterm.of_lookup t lookup [] .external
    rcases occ.last_departure with ⟨empty,_⟩ | ⟨other,s,sub,split,atParent,departure⟩
    · have lengths:=congrArg List.length empty; simp at lengths
    · have lengths:=congrArg List.length split
      have sameParent : parent=other := List.append_inj_left split (by simp only [List.length_append,List.length_singleton] at lengths;omega)
      have sameStep : step=s := by
        rw [sameParent] at split
        exact (List.cons.inj (List.append_cancel_left split)).1
      subst other;subst s
      have turn : GraphTurn ctx left := by
        cases departure with
        | fn => exact False.elim (notFunction rfl)
        | arg => rw [starts_app atParent start];exact .symm (.appFnArg _)
        | body => rw [starts_lam atParent start];exact .symm (.lamContextBody _)
      refine ⟨.lamContext stamp,right,starts_lam_intro lookup,?_⟩
      have both := GraphWalk.join (edge_forward initial occ).reverse turn walk
      simp only [signed,positions_cons _ tail.chain,List.zipWith_cons_cons,List.flatten_cons,
        Bool.false_eq_true,if_false]
      rw [selected_label selection _ lookup]
      exact both
  | @var leaf stamp index parent origin body rest es ds lookup binder split depth tail ih =>
    obtain ⟨left,right,start,walk⟩ := ih
    have port := starts_lam binder start
    subst left
    let v : SyntaxIncidence.ProperPosition t := ⟨parent,Or.inr ⟨origin,body,binder⟩⟩
    refine ⟨.lamContext origin,right,⟨v,Or.inr ⟨stamp,index,origin,body,rest,lookup,binder,split,depth⟩,
      Or.inr ⟨origin,body,binder,rfl⟩⟩,?_⟩
    exact walk

/-- A genuine INIT reading gives a signed source-graph walk, retaining the
same chosen literal blocks. This asserts no whole Forward physical path. -/
theorem initial_reading_signed_graph_walk
    {current : LTerm} {g : Net signature N B W} {root : B}
    {start : Path} {edges : List Path} {directions : List Bool}
    (initial : INIT current)
    (reading : PrerequisiteReading current start edges directions)
    (selection : OccurrenceFragmentSelection current g root) :
    ∃ positions : List (Position current.erase),
      positions.map (fun position => position.val) = edges ∧
      canonicalChainImage selection reading.chain =
        positions.map (fun position => (selection position).fragment.segments) ∧
      orientedChainImage selection reading =
        List.zipWith (fun position forward => (selection position).read forward) positions directions ∧
      ∃ (first : SyntaxIncidence.ProperPosition current) (a b : SourcePort),
        SyntaxIncidence.Target current start (some first) ∧
        ((∃ stamp fn arg, current.subterm first.val = some (.app stamp fn arg) ∧ a = .appFn stamp) ∨
          (∃ stamp body, current.subterm first.val = some (.lam stamp body) ∧ a = .lamContext stamp)) ∧
        GraphWalk (sourceEdges [] .external current) a
          (List.flatten (List.zipWith (fun position forward =>
            if forward then (selection position).term.label.edgeWord
            else EdgeWord.reverse (selection position).term.label.edgeWord) positions directions)) b := by
  obtain ⟨a,b,⟨first,target,kind⟩,walk⟩ := signed_walk initial selection reading
  refine ⟨positions reading.chain,positions_values _,?_,?_,first,a,b,target,kind,walk⟩
  · simp only [canonicalChainImage,positions,List.map_map]
    apply List.map_congr_left
    intro edge member
    rfl
  · simp only [orientedChainImage,canonicalChainImage,positions,
      List.zipWith_map_left,OccurrenceFragment.read]
    rfl

end
#print axioms initial_reading_signed_graph_walk
end Lamping.AG
