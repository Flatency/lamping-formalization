import Lamping.Lamping.GeneratedExpandedLoops
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- Finite loop expansion with the previous rooted body retained at each
event. Actual histories must construct these supports from their previous
state; this is not asserted for every GeneratedExpandedBindingLoop. -/
inductive SupportedExpandedBindingLoop (root : B) :
    List (Endpoint g) → N → List (Endpoint g) → Prop
  | base (ambient es : List (Endpoint g)) (a b : Context)
      (binding : BindingLoop g es a b) :
      SupportedExpandedBindingLoop root ambient binding.binder es
  | insert (ambient : List (Endpoint g)) (binder : N) (edge : BetaEdge g)
      (pre inner tail : List (Endpoint g))
      (outer : SupportedExpandedBindingLoop root ambient binder (pre++edge.argEnd::tail))
      (nested : SupportedExpandedBindingLoop root (ambient++pre++edge.principal) edge.lam inner)
      (previousBody : GeneratedExpandedProperPath g root (ambient++(pre++edge.argEnd::tail)))
      (nestedBody : GeneratedExpandedProperPath g root (ambient++pre++edge.principal++inner))
      (preEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
      (innerStart : inner.head?=some (.inl ⟨edge.lam,edge.lamBody⟩))
      (innerEnd : inner.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩))) :
      SupportedExpandedBindingLoop root ambient binder
        (pre++edge.principal++inner++edge.reverseRoute++[edge.argEnd]++tail)

variable {g}
theorem SupportedExpandedBindingLoop.erase {root ambient binder es}
    (support : SupportedExpandedBindingLoop g root ambient binder es) :
    GeneratedExpandedBindingLoop g root ambient binder es := by
  induction support with
  | base ambient es a b binding => exact .base ambient es a b binding
  | insert ambient binder edge pre inner tail _ _ _ nestedBody preEnd innerStart innerEnd outerIH nestedIH =>
    exact .insert ambient binder edge pre inner tail outerIH nestedIH nestedBody preEnd innerStart innerEnd

/-- Insert a supplied supported loop using ordinary generation constructors.
Only earlier residual bodies are stored in the support. The new inserted
path is constructed, and no converse from bare generated loops is claimed. -/
theorem SupportedExpandedBindingLoop.insert_admissible
    {root ambient binder loop}
    (support : SupportedExpandedBindingLoop g root ambient binder loop)
    (edge : BetaEdge g) (stem suffix : List (Endpoint g))
    (ambientEq : ambient=stem++edge.principal) (sameBinder : binder=edge.lam)
    (argument : GeneratedExpandedProperPath g root (stem++edge.argEnd::suffix))
    (body : GeneratedExpandedProperPath g root (ambient++loop))
    (stemEnd : stem.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩)))
    (loopStart : loop.head?=some (.inl ⟨edge.lam,edge.lamBody⟩))
    (loopEnd : loop.getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩))) :
    GeneratedExpandedProperPath g root
      (stem++edge.principal++loop++edge.reverseRoute++[edge.argEnd]++suffix) := by
  induction support generalizing edge stem suffix with
  | base ambient es a b binding =>
    exact GeneratedExpandedProperPath.insert edge stem es suffix argument
      (by simpa only [ambientEq] using body) stemEnd loopStart loopEnd a b binding sameBinder
  | insert ambient binder inner pre innerLoop tail outer nested previousBody nestedBody preEnd innerStart innerEnd outerIH nestedIH =>
    have preNonempty : pre≠[] := by intro empty; rw [empty] at preEnd; cases preEnd
    have oldStart : (pre++inner.argEnd::tail).head?=some (.inl ⟨edge.lam,edge.lamBody⟩) := by
      cases pre with
      | nil => exact False.elim (preNonempty rfl)
      | cons x xs => exact loopStart
    have oldEnd : (pre++inner.argEnd::tail).getLast?=some (g.wire (.inl ⟨edge.lam,edge.lamBind⟩)) := by
      cases last : tail.getLast? <;>
        simpa [List.getLast?_append,List.getLast?_cons,last] using loopEnd
    have first := outerIH edge stem suffix ambientEq sameBinder argument previousBody stemEnd oldStart oldEnd
    have nextArgument : GeneratedExpandedProperPath g root
        ((stem++edge.principal++pre)++inner.argEnd::(tail++edge.reverseRoute++[edge.argEnd]++suffix)) := by
      simpa only [List.append_assoc,List.cons_append,List.singleton_append] using first
    have nextEnd : (stem++edge.principal++pre).getLast?=some (g.wire (.inl ⟨inner.app,inner.appCtx⟩)) := by
      simp only [List.getLast?_append,preEnd,Option.some_or]
    have nextAmbient : ambient++pre++inner.principal=(stem++edge.principal++pre)++inner.principal := by rw [ambientEq]
    have last := nestedIH inner (stem++edge.principal++pre)
      (tail++edge.reverseRoute++[edge.argEnd]++suffix) nextAmbient rfl nextArgument
      nestedBody nextEnd innerStart innerEnd
    simpa only [List.append_assoc] using last
end
end Lamping.AG
