import Lamping.Lamping.ExpandedPaths
import Lamping.Lamping.LocalTransport
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Every explicit insertion has room for a prefix segment, a principal
segment, the binding loop, a reverse segment, and the argument departure. -/
theorem ExpandedProperPath.short_is_ordinary
    (loops : ∀ (es : List (Endpoint g)) (a b : Context), BindingLoop g es a b → 2 ≤ es.length)
    {root : B} {es : List (Endpoint g)} (h : ExpandedProperPath g root es)
    (short : es.length ≤ 5) : ForwardProperPath g es := by
  cases h with
  | base path _ => exact path
  | insert r pre loop suffix argument body preEnd loopStart loopEnd a b binding same =>
    have hl := loops loop a b binding
    have hp : 0 < pre.length := by
      cases pre with
      | nil => simp at preEnd
      | cons => simp
    have hr : 0 < r.principal.length := by
      have hs := r.principalStart
      apply List.length_pos_iff.mpr
      intro he
      rw [he] at hs
      cases hs
    have hrev : r.reverseRoute.length = r.principal.length := by
      simp [BetaEdge.reverseRoute]
    simp only [List.length_append,List.length_cons,List.length_nil] at short
    omega

/-- Nonempty physical prefixes of the original least generation. This does not
assert equality with the unclosed relation: reverse-route truncation is new. -/
def PrefixExpandedProperPath (root : B) (es : List (Endpoint g)) : Prop :=
  es ≠ [] ∧ ∃ suffix, ExpandedProperPath g root (es ++ suffix)

theorem ExpandedProperPath.prefixClosure {root : B} {es : List (Endpoint g)}
    (h : ExpandedProperPath g root es) : PrefixExpandedProperPath (g:=g) root es := by
  refine ⟨?_,[],by simpa using h⟩
  intro he
  have hr := expanded_rooted g h
  rw [he] at hr
  cases hr

theorem PrefixExpandedProperPath.prefix {root : B} {es suffix : List (Endpoint g)}
    (h : PrefixExpandedProperPath (g:=g) root (es++suffix)) (nonempty : es≠[]) :
    PrefixExpandedProperPath (g:=g) root es := by
  obtain ⟨_,tail,generated⟩ := h
  exact ⟨nonempty,suffix++tail,by simpa only [List.append_assoc] using generated⟩

theorem PrefixExpandedProperPath.rooted {root : B} {es : List (Endpoint g)}
    (h : PrefixExpandedProperPath (g:=g) root es) : es.head?=some (.inr (.inl root)) := by
  obtain ⟨nonempty,tail,generated⟩ := h
  have hr := expanded_rooted g generated
  cases es with
  | nil => exact False.elim (nonempty rfl)
  | cons e es => simpa only [List.cons_append,List.head?_cons] using hr

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

theorem PrefixExpandedProperPath.forward {root : B} {es : List (Endpoint g)}
    (h : PrefixExpandedProperPath (g:=g) root es) : ExpandedForward g es := by
  obtain ⟨nonempty,tail,generated⟩ := h
  exact expandedForward_prefix generated.forward nonempty

/-- This is the least nonempty-prefix-closed predicate containing the old
relation. It supplies generation induction, not a labelability certificate. -/
theorem PrefixExpandedProperPath.least (P : List (Endpoint g) → Prop)
    (base : ∀ es, ExpandedProperPath g root es → P es)
    (closedPrefix : ∀ es suffix, P (es++suffix) → es≠[] → P es)
    {es : List (Endpoint g)} (h : PrefixExpandedProperPath (g:=g) root es) : P es := by
  obtain ⟨nonempty,suffix,generated⟩ := h
  exact closedPrefix es suffix (base _ generated) nonempty
end
end Lamping.AG




