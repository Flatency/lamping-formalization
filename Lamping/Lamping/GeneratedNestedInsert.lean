import Lamping.Lamping.GeneratedExpandedLoops
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- One genuine recursive loop expansion can be inserted by two ordinary
insertion rules. The reduced outer body is retained explicitly: this lemma
is the finite interchange step, not the unproved general Ex.3.5.20 closure. -/
theorem GeneratedExpandedProperPath.nested_insert
    (outer inner : BetaEdge g) (stem pre loop tail suffix : List (Endpoint g))
    (a b c d : Context)
    (outerBinding : BindingLoop g (pre++inner.argEnd::tail) a b)
    (innerBinding : BindingLoop g loop c d)
    (outerBinder : outerBinding.binder=outer.lam)
    (innerBinder : innerBinding.binder=inner.lam)
    (stemEnd : stem.getLast?=some (g.wire (.inl ⟨outer.app,outer.appCtx⟩)))
    (outerStart : (pre++inner.argEnd::tail).head?=some (.inl ⟨outer.lam,outer.lamBody⟩))
    (outerEnd : (pre++inner.argEnd::tail).getLast?=some (g.wire (.inl ⟨outer.lam,outer.lamBind⟩)))
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨inner.app,inner.appCtx⟩)))
    (innerStart : loop.head?=some (.inl ⟨inner.lam,inner.lamBody⟩))
    (innerEnd : loop.getLast?=some (g.wire (.inl ⟨inner.lam,inner.lamBind⟩)))
    (argument : GeneratedExpandedProperPath g root (stem++outer.argEnd::suffix))
    (reducedBody : GeneratedExpandedProperPath g root
      (stem++outer.principal++(pre++inner.argEnd::tail)))
    (nestedBody : GeneratedExpandedProperPath g root
      ((stem++outer.principal++pre)++inner.principal++loop)) :
    GeneratedExpandedProperPath g root
      (stem++outer.principal++
        (pre++inner.principal++loop++inner.reverseRoute++[inner.argEnd]++tail)++
        outer.reverseRoute++[outer.argEnd]++suffix) := by
  have outerFirst := GeneratedExpandedProperPath.insert outer stem
    (pre++inner.argEnd::tail) suffix argument reducedBody stemEnd outerStart outerEnd
    a b outerBinding outerBinder
  have argument' : GeneratedExpandedProperPath g root
      ((stem++outer.principal++pre)++inner.argEnd::
        (tail++outer.reverseRoute++[outer.argEnd]++suffix)) := by
    simpa only [List.append_assoc,List.cons_append,List.singleton_append] using outerFirst
  have preEnd' : (stem++outer.principal++pre).getLast?=
      some (g.wire (.inl ⟨inner.app,inner.appCtx⟩)) := by
    simp only [List.getLast?_append,preEnd,Option.some_or]
  have innerLast := GeneratedExpandedProperPath.insert inner
    (stem++outer.principal++pre) loop (tail++outer.reverseRoute++[outer.argEnd]++suffix)
    argument' nestedBody preEnd' innerStart innerEnd c d innerBinding innerBinder
  simpa only [List.append_assoc] using innerLast
end
end Lamping.AG
