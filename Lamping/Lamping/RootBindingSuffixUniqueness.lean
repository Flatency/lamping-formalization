import Lamping.Lamping.RootBinderUniform
import Lamping.Lamping.BindingSuffixUniqueness
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Weak root inputs transport the original binder candidate between actual
assignments; Nesting then locks the exact literal occurrence and suffix. -/
theorem RootInputs.binder_split_unique {root : B}
    (inputs : RootInputs g root) (nesting : Nesting g root) (transparency : Transparency g root)
    (node : N) (ctx body bind : Port (g.label node).sort) (level : Nat)
    (nodeLabel : g.label node=label .lam level)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (es pre loop other rest : List (Endpoint g))
    (input middle output otherInput otherMiddle otherOutput : Context)
    (rooted : es.head?=some (.inr (.inl root))) (forward : Forward g es)
    (finish : es.getLast?=some (g.wire (.inl ⟨node,bind⟩)))
    (firstLabels : Labelling g es input output)
    (secondLabels : Labelling g es otherInput otherOutput)
    (first : es=pre++loop) (second : es=other++rest)
    (prefixLabels : Labelling g pre input middle)
    (otherLabels : Labelling g other otherInput otherMiddle)
    (prefixEnd : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (otherEnd : other.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (shell : Context.SameShell level middle output)
    (otherShell : Context.SameShell level otherMiddle otherOutput) :
    pre=other ∧ loop=rest := by
  obtain ⟨cs,trace,head,_last⟩ := firstLabels.contextTrace g
  have otherNonempty := otherLabels.nonempty
  have positive := List.length_pos_iff.mpr otherNonempty
  have within : other.length-1<cs.length := by
    have lengths := trace.length g
    rw [second,List.length_append] at lengths
    omega
  let chosen := cs[other.length-1]
  have point : cs[other.length-1]?=some chosen := List.getElem?_eq_getElem within
  have otherAtInput := trace.prefix_labels (other.length-1) point head
  have takeEq : es.take (other.length-1+1)=other := by
    rw [Nat.sub_add_cancel (by omega),second,List.take_left]
  rw [takeEq] at otherAtInput
  have transported := Marker.binder_shell_stable_node_rootInputs inputs nesting
    transparency node ctx body bind level nodeLabel ctxRole bodyRole bindRole
    es other rest otherInput otherMiddle otherOutput rooted forward finish secondLabels second
    otherLabels otherEnd otherShell input chosen output firstLabels otherAtInput
  have atRole : AtProperRole g root (g.wire (g.wire (.inl ⟨node,ctx⟩))) .lamCtx level := by
    simpa only [Pairing.involutive] using
      AtProperRole.lamCtx (g:=g) (root:=root) node ctx level nodeLabel ctxRole
  exact nesting.binding_split_unique rooted forward trace input output middle chosen head
    pre loop other rest first second prefixLabels.nonempty otherNonempty prefixLabels otherAtInput
    (g.wire (.inl ⟨node,ctx⟩)) prefixEnd otherEnd .lamCtx level (Or.inr rfl) atRole shell transported

/-- Two genuine binding suffixes of one actual root access have the same
index, using root-input totality and the actual ordinary N/T properties.
No arbitrary non-root input or full Independence is assumed. -/
theorem RootInputs.binding_suffix_unique {root : B}
    (inputs : RootInputs g root) (nesting : Nesting g root) (transparency : Transparency g root) (path : RootAccess g root)
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
  obtain ⟨_samePre,sameLoop⟩ := inputs.binder_split_unique nesting transparency node ctx body bind
    (g.label node).index nodeLabel ctxRole bodyRole bindRole path.val pre loop other rest
    a b c a' b' c' path.property.2.1 path.property.1.2 finish whole whole' first second
    preLabels otherLabels preEnd otherEnd shell shell'
  exact index.trans ((congrArg (fun xs => binderDepth (accessWord g xs)) sameLoop).trans index'.symm)
end
end Lamping.AG
