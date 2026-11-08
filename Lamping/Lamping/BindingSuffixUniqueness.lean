import Lamping.Lamping.OrdinaryBinderOccurrences
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem lambda_body_turn (k : Kind) (i : Nat) (ctx body : Port k)
    (isLam : k=.op .lam) (hc : HEq ctx (Sum.inl () : Port (.op .lam)))
    (hb : HEq body lamBody) (a : Context) : Traversal i k ctx body a a := by
  subst k
  have hc' : ctx=.inl () := eq_of_heq hc
  have hb' : body=lamBody := eq_of_heq hb
  subst ctx; subst body
  exact .direct (.lamBody a)

/-- Glue the actual suffix witness using its own seam assignment. -/
theorem BindingLoop.prefix_labelling {pre loop : List (Endpoint g)} {a b c : Context}
    (binding : BindingLoop g loop b c) (ctx : Port (g.label binding.binder).sort)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)))
    (prefixLabels : Labelling g pre a b) : Labelling g (pre++loop) a c := by
  obtain ⟨xs,preSplit⟩ := List.getLast?_eq_some_iff.mp prefixEnd
  obtain ⟨ys,loopSplit⟩ := List.head?_eq_some_iff.mp binding.start
  have seam : LabelledTurn g (.inl ⟨binding.binder,ctx⟩)
      (.inl ⟨binding.binder,binding.body⟩) b b :=
    .node binding.binder ctx binding.body
      (lambda_body_turn _ _ _ _ binding.isLam ctxRole binding.body_role b)
  rw [preSplit] at prefixLabels
  have loopLabels := binding.proper
  rw [loopSplit] at loopLabels
  have glued := prefixLabels.splice loopLabels (by simpa only [Pairing.involutive] using seam)
  simpa only [preSplit,loopSplit,List.append_assoc,List.singleton_append] using glued

/-- Ordinary invariants identify the binder occurrence and hence the de Bruijn
index for every pair of genuine BindingSuffix witnesses of a root access. -/
theorem OrdinaryPathInvariants.binding_suffix_unique {root : B}
    (invariants : OrdinaryPathInvariants g root) (path : RootAccess g root)
    {i j : Nat} (firstSuffix : BindingSuffix g path.val i)
    (secondSuffix : BindingSuffix g path.val j) : i=j := by
  obtain ⟨pre,loop,a,b,c,binding,ctx,first,ctxRole,preEnd,preLabels,index⟩ := firstSuffix
  obtain ⟨other,rest,a',b',c',binding',ctx',second,ctxRole',otherEnd,otherLabels,index'⟩ := secondSuffix
  have finish : path.val.getLast?=some (g.wire (.inl ⟨binding.binder,binding.bind⟩)) := by
    rw [first,List.getLast?_append,binding.finish,Option.some_or]
  have finish' : path.val.getLast?=some (g.wire (.inl ⟨binding'.binder,binding'.bind⟩)) := by
    rw [second,List.getLast?_append,binding'.finish,Option.some_or]
  have endpointEq : (.inl ⟨binding.binder,binding.bind⟩ : Endpoint g)=
      .inl ⟨binding'.binder,binding'.bind⟩ := by
    have equal := congrArg g.wire (Option.some.inj (finish.symm.trans finish'))
    simpa only [Pairing.involutive] using equal
  have binderEq : binding.binder=binding'.binder := congrArg Sigma.fst (Sum.inl.inj endpointEq)
  rcases binding with ⟨node,isLam,body,bind,bodyRole,bindRole,start,last,labels,fw,shell⟩
  rcases binding' with ⟨node',isLam',body',bind',bodyRole',bindRole',start',last',labels',fw',shell'⟩
  dsimp at binderEq
  subst node'
  have sameCtx : ctx'=ctx := eq_of_heq (ctxRole'.trans ctxRole.symm)
  subst ctx'
  have nodeLabel : g.label node=label .lam (g.label node).index := by
    cases h : g.label node with
    | mk sort level => simp only [h] at isLam; cases isLam; rfl
  have whole := BindingLoop.prefix_labelling
    (BindingLoop.mk node isLam body bind bodyRole bindRole start last labels fw shell) ctx ctxRole preEnd preLabels
  have whole' := BindingLoop.prefix_labelling
    (BindingLoop.mk node isLam' body' bind' bodyRole' bindRole' start' last' labels' fw' shell') ctx ctxRole otherEnd otherLabels
  rw [←first] at whole
  rw [←second] at whole'
  obtain ⟨_samePre,sameLoop⟩ := invariants.binder_split_unique node ctx body bind
    (g.label node).index nodeLabel ctxRole bodyRole bindRole path.val pre loop other rest
    a b c a' b' c' path.property.2.1 path.property.1.2 finish whole whole' first second
    preLabels otherLabels preEnd otherEnd shell shell'
  exact index.trans ((congrArg (fun xs => binderDepth (accessWord g xs)) sameLoop).trans index'.symm)
end
end Lamping.AG
