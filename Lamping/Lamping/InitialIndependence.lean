import Lamping.Lamping.InitialPathLevels
import Lamping.Lamping.InitialNesting
namespace Lamping.AG
open Graph Lambda
private theorem last_append_nonempty {T : Type} (xs ys : List T) (nonempty : ys≠[]) :
    (xs++ys).getLast?=ys.getLast? := by
  rw [List.getLast?_append]
  cases h : ys.getLast? with
  | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp h))
  | some => rfl

/-- A given initial proper-source path ending at an app/lambda context has
no control effect. Its exact input and output contexts are equal. -/
theorem encode_source_context_unchanged (t : Term) (level : Nat)
    (es : List (Endpoint (encode level t).net)) (e f : Endpoint (encode level t).net)
    (sr tr : ProperRole) (m n : Nat)
    (source : AtProperRole (encode level t).net (.inl ()) e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole (encode level t).net (.inl ()) f tr n) (context : tr=.appCtx ∨tr=.lamCtx)
    (head : es.head?=some e) (last : es.getLast?=some ((encode level t).net.wire f))
    (labels : Labelling (encode level t).net es a b) : a=b := by
  obtain ⟨pre,rooted,prefixLabels⟩ := encode_source_identity_prefix t level e sr m source outgoing
  cases es with
  | nil => cases head
  | cons first tail =>
    have same : first=e := Option.some.inj head
    subst first
    have whole := (prefixLabels a).join labels
    have wholeRoot : (pre++e::tail).head?=some (.inr (.inl (.inl ()))) := by
      cases pre <;> exact rooted
    have wholeLast : (pre++e::tail).getLast?=some ((encode level t).net.wire f) := by
      rw [last_append_nonempty pre (e::tail) (by simp)]
      exact last
    obtain ⟨addr⟩ := encode_addressing t level
    obtain ⟨word,kind,atPort,_⟩ := target.context_address context addr.nodes (boundaryAddressAt []) addr.vertices
    have atExit : endpointAddress (encode level t).net addr.nodes (boundaryAddressAt []) addr.vertices
        ((encode level t).net.wire f)=some word := (addr.wiring f).trans atPort
    exact addr.path_context _ (encode_root_initial t level _ wholeRoot whole) _ wholeLast word atExit

/-- The complete initial Independence conclusion for app/lambda context
terminals. Binding terminals require the separate offset-program branch and
are not included in this theorem. -/
theorem encode_context_target_independence (t : Term) (level : Nat)
    (es : List (Endpoint (encode level t).net)) (e f : Endpoint (encode level t).net)
    (sr tr : ProperRole) (m n : Nat) (a b : Context)
    (source : AtProperRole (encode level t).net (.inl ()) e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole (encode level t).net (.inl ()) f tr n) (context : tr=.appCtx ∨tr=.lamCtx)
    (head : es.head?=some e) (last : es.getLast?=some ((encode level t).net.wire f))
    (labels : Labelling (encode level t).net es a b) :
    (∀ x,∃ output,Labelling (encode level t).net es (a.replace m x) output) ∧
    ∃ width,m≤width ∧(sr=.appArg → m<width) ∧
      (∀ c,b=b.replace (tr.terminalWidth n) c → a=a.replace width c) ∧
      (∀ y,Labelling (encode level t).net es (a.replace width y) (b.replace (tr.terminalWidth n) y)) := by
  have equal := encode_source_context_unchanged t level es e f sr tr m n source outgoing target context head last labels
  subst b
  have widthEq : tr.terminalWidth n=n := by rcases context with eq | eq <;> subst tr <;> rfl
  obtain ⟨lower,strict⟩ := encode_source_context_levels t level es e f sr tr m n source outgoing target context head last labels
  refine ⟨fun x => encode_source_relabel t level es e sr m source outgoing head labels (a.replace m x),
    n,lower,strict,?_,?_⟩
  · intro c fixed
    rw [widthEq] at fixed
    exact fixed
  · intro y
    rw [widthEq]
    obtain ⟨output,changed⟩ := encode_source_relabel t level es e sr m source outgoing head labels (a.replace n y)
    have same := encode_source_context_unchanged t level es e f sr tr m n source outgoing target context head last changed
    rw [←same] at changed
    exact changed
end Lamping.AG
