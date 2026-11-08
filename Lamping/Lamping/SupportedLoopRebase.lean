import Lamping.Lamping.SupportedLoopPorts
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Conditional naturality of the finite support tree. The hypothesis is
explicit prefix transport, not a claimed general generated-path closure.
The concrete copy theorem below constructs this transport by insertion. -/
theorem SupportedExpandedBindingLoop.rebase {oldAmbient binder loop}
    (support : SupportedExpandedBindingLoop g root oldAmbient binder loop)
    (newAmbient : List (Endpoint g))
    (transport : ∀ suffix,GeneratedExpandedProperPath g root (oldAmbient++suffix) →
      GeneratedExpandedProperPath g root (newAmbient++suffix)) :
    SupportedExpandedBindingLoop g root newAmbient binder loop := by
  induction support generalizing newAmbient with
  | base ambient es a b binding => exact .base newAmbient es a b binding
  | insert ambient binder edge pre inner tail outer nested previousBody nestedBody preEnd innerStart innerEnd outerIH nestedIH =>
    have newOuter := outerIH newAmbient transport
    have newNested := nestedIH (newAmbient++pre++edge.principal) (by
      intro suffix generated
      have previous : GeneratedExpandedProperPath g root (ambient++(pre++edge.principal++suffix)) := by
        simpa only [List.append_assoc] using generated
      have next := transport (pre++edge.principal++suffix) previous
      simpa only [List.append_assoc] using next)
    have newPrevious := transport (pre++edge.argEnd::tail) previousBody
    have newBody : GeneratedExpandedProperPath g root (newAmbient++pre++edge.principal++inner) := by
      have previous : GeneratedExpandedProperPath g root (ambient++(pre++edge.principal++inner)) := by
        simpa only [List.append_assoc] using nestedBody
      have next := transport (pre++edge.principal++inner) previous
      simpa only [List.append_assoc] using next
    exact .insert newAmbient binder edge pre inner tail newOuter newNested newPrevious newBody preEnd innerStart innerEnd

/-- Rebase an already supported argument binder through a genuine outer
copy detour. Every earlier body in the copied support is transported by the
proved finite insertion theorem, with an arbitrary suffix. No new-ambient
generatedness certificate or general completion hypothesis is an input. -/
theorem SupportedExpandedBindingLoop.copy_rebase
    (edge : BetaEdge g) (stem outerLoop pre : List (Endpoint g))
    (outer : SupportedExpandedBindingLoop g root (stem++edge.principal) edge.lam outerLoop)
    (body : GeneratedExpandedProperPath g root (stem++edge.principal++outerLoop))
    (stemEnd : stem.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    {binder loop}
    (copied : SupportedExpandedBindingLoop g root (stem++edge.argEnd::pre) binder loop) :
    SupportedExpandedBindingLoop g root
      (stem++edge.principal++outerLoop++edge.reverseRoute++[edge.argEnd]++pre) binder loop := by
  apply copied.rebase
  intro suffix generated
  have argument : GeneratedExpandedProperPath g root (stem++edge.argEnd::(pre++suffix)) := by
    simpa only [List.append_assoc,List.cons_append] using generated
  have inserted := outer.insert_at_beta edge stem (pre++suffix) rfl rfl argument body stemEnd
  simpa only [List.append_assoc] using inserted
end
end Lamping.AG
