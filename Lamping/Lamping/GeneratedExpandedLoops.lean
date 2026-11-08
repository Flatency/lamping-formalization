import Lamping.Lamping.ExpandedPrefixClosure
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- Source Def.3.5.16 with the nonempty physical-prefix closure required by
Ex.3.5.18. Generation is separate from proper labellability and soundness. -/
inductive GeneratedExpandedProperPath (root : B) : List (Endpoint g) → Prop
  | base {es} (path : ForwardProperPath g es)
      (rooted : es.head?=some (.inr (.inl root))) : GeneratedExpandedProperPath root es
  | insert (r : BetaEdge g) (pre loop suffix : List (Endpoint g))
      (argument : GeneratedExpandedProperPath root (pre ++ r.argEnd::suffix))
      (body : GeneratedExpandedProperPath root (pre ++ r.principal ++ loop))
      (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)))
      (loopStart : loop.head?=some (.inl ⟨r.lam,r.lamBody⟩))
      (loopEnd : loop.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)))
      (a b : Context) (binding : BindingLoop g loop a b)
      (sameBinder : binding.binder=r.lam) :
      GeneratedExpandedProperPath root
        (pre ++ r.principal ++ loop ++ r.reverseRoute ++ [r.argEnd] ++ suffix)
  | takePrefix {es suffix} (path : GeneratedExpandedProperPath root (es++suffix))
      (nonempty : es≠[]) : GeneratedExpandedProperPath root es

 theorem ExpandedProperPath.generated {root : B} {es : List (Endpoint g)}
    (h : ExpandedProperPath g root es) : GeneratedExpandedProperPath g root es := by
  induction h with
  | base hp hr => exact .base hp hr
  | insert r pre loop suffix argument body preEnd loopStart loopEnd a b binding same ia ib =>
    exact .insert r pre loop suffix ia ib preEnd loopStart loopEnd a b binding same

 theorem PrefixExpandedProperPath.generated {root : B} {es : List (Endpoint g)}
    (h : PrefixExpandedProperPath (g:=g) root es) : GeneratedExpandedProperPath g root es := by
  obtain ⟨nonempty,suffix,path⟩ := h
  exact .takePrefix (path.generated g) nonempty

 theorem GeneratedExpandedProperPath.rooted {root : B} {es : List (Endpoint g)}
    (h : GeneratedExpandedProperPath g root es) : es.head?=some (.inr (.inl root)) := by
  induction h with
  | base _ hr => exact hr
  | insert r pre loop suffix _ _ preEnd _ _ _ _ _ _ ih _ =>
    cases pre with
    | nil => simp at preEnd
    | cons e rest => simpa using ih
  | @takePrefix es suffix path nonempty ih =>
    cases es with
    | nil => exact False.elim (nonempty rfl)
    | cons e rest => simpa only [List.cons_append,List.head?_cons] using ih

private theorem expandedForward_prefix {es suffix : List (Endpoint g)}
    (h : ExpandedForward g (es++suffix)) (nonempty : es≠[]) : ExpandedForward g es := by
  induction es with
  | nil => exact False.elim (nonempty rfl)
  | cons e es ih =>
    cases es with
    | nil => exact .single e
    | cons f es =>
      cases h with
      | cons ht hs => exact .cons ht (ih hs (by simp))

 theorem GeneratedExpandedProperPath.forward {root : B} {es : List (Endpoint g)}
    (h : GeneratedExpandedProperPath g root es) : ExpandedForward g es := by
  induction h with
  | base path _ => exact path.2.expanded
  | insert r pre loop suffix _ _ _ _ loopEnd _ _ _ _ argIH bodyIH =>
    have arg := argIH.of_append (by simp : r.argEnd::suffix≠[])
    have rev := r.reverse_forward.expanded
    have bodyEnd : (pre++r.principal++loop).getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)) := by
      simp only [List.getLast?_append,loopEnd,Option.some_or]
    have first : ExpandedForward g ((pre++r.principal++loop)++r.reverseRoute) := by
      apply bodyIH.splice bodyEnd rev r.reverse_start
      simpa only [Pairing.involutive] using ExpandedDirection.bindToCtx (g:=g) r
    have firstEnd : ((pre++r.principal++loop)++r.reverseRoute).getLast?=some (g.wire r.funEnd) := by
      simp only [List.getLast?_append,r.reverse_finish,Option.some_or]
    have final := first.splice firstEnd arg rfl
      (by simpa only [Pairing.involutive] using ExpandedDirection.funToArg (g:=g) r)
    simpa only [List.append_assoc,List.singleton_append] using final
  | takePrefix path nonempty ih => exact expandedForward_prefix g ih nonempty


/-- Explicit leastness/induction API for the new physical-prefix generation.
This is usable to prove invariants simultaneously; it does not assert them. -/
theorem GeneratedExpandedProperPath.least (root : B) (P : List (Endpoint g) → Prop)
    (baseCase : ∀ es, ForwardProperPath g es →
      es.head?=some (.inr (.inl root)) → P es)
    (insertCase : ∀ (r : BetaEdge g) pre loop suffix (a b : Context)
      (binding : BindingLoop g loop a b),
      pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)) →
      loop.head?=some (.inl ⟨r.lam,r.lamBody⟩) →
      loop.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)) → binding.binder=r.lam →
      P (pre++r.argEnd::suffix) → P (pre++r.principal++loop) →
      P (pre++r.principal++loop++r.reverseRoute++[r.argEnd]++suffix))
    (prefixCase : ∀ es suffix, P (es++suffix) → es≠[] → P es)
    {es : List (Endpoint g)} (h : GeneratedExpandedProperPath g root es) : P es := by
  induction h with
  | base path rooted => exact baseCase _ path rooted
  | insert r pre loop suffix _ _ preEnd loopStart loopEnd a b binding same ia ib =>
    exact insertCase r pre loop suffix a b binding preEnd loopStart loopEnd same ia ib
  | takePrefix path nonempty ih => exact prefixCase _ _ ih nonempty
/-- The exact generated-loop recursion of Ex.3.5.20, with the ambient root
prefix explicitly retained in its body-path premise. Its insertion admissibility
and proper labelling are separate obligations; neither is an input certificate. -/
inductive GeneratedExpandedBindingLoop (root : B) :
    List (Endpoint g) → N → List (Endpoint g) → Prop
  | base (stem : List (Endpoint g)) (es : List (Endpoint g)) (a b : Context)
      (binding : BindingLoop g es a b) :
      GeneratedExpandedBindingLoop root stem binding.binder es
  | insert (stem : List (Endpoint g)) (binder : N) (r : BetaEdge g)
      (pre inner suffix : List (Endpoint g))
      (outer : GeneratedExpandedBindingLoop root stem binder (pre ++ r.argEnd::suffix))
      (nested : GeneratedExpandedBindingLoop root (stem++pre++r.principal) r.lam inner)
      (body : GeneratedExpandedProperPath g root (stem++pre++r.principal++inner))
      (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)))
      (innerStart : inner.head?=some (.inl ⟨r.lam,r.lamBody⟩))
      (innerEnd : inner.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩))) :
      GeneratedExpandedBindingLoop root stem binder
        (pre ++ r.principal ++ inner ++ r.reverseRoute ++ [r.argEnd] ++ suffix)

end
end Lamping.AG


