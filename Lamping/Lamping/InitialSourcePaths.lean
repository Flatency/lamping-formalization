import Lamping.Lamping.EncodedHeights
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph Lambda
private theorem app_fun_predecessor {kind : Kind} (level : Nat) (q : Port kind)
    (isApp : kind=.op .app) (role : HEq q (Sum.inl () : Port (.op .app))) :
    ∃ p : Port kind,IsContextPort kind p ∧∀ input,Traversal level kind p q input input := by
  subst kind
  have same : q=.inl () := eq_of_heq role
  subst q
  exact ⟨appCtx,Or.inl rfl,fun input => .direct (.appFun input)⟩
private theorem app_arg_predecessor {kind : Kind} (level : Nat) (q : Port kind)
    (isApp : kind=.op .app) (role : HEq q appArg) :
    ∃ p : Port kind,IsContextPort kind p ∧∀ input,Traversal level kind p q input input := by
  subst kind
  have same : q=appArg := eq_of_heq role
  subst q
  exact ⟨appCtx,Or.inl rfl,fun input => .direct (.appArg input)⟩
private theorem lam_body_predecessor {kind : Kind} (level : Nat) (q : Port kind)
    (isLam : kind=.op .lam) (role : HEq q lamBody) :
    ∃ p : Port kind,IsContextPort kind p ∧∀ input,Traversal level kind p q input input := by
  subst kind
  have same : q=lamBody := eq_of_heq role
  subst q
  exact ⟨.inl (),Or.inr rfl,fun input => .direct (.lamBody input)⟩

private theorem source_turn {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {g : Net signature N B W} {node : N} {q : Port (g.label node).sort} {root : B} {role : ProperRole} {m : Nat}
    (source : AtProperRole g root (.inl ⟨node,q⟩) role m) (outgoing : role.outgoing) :
    ∃ p : Port (g.label node).sort,IsContextPort (g.label node).sort p ∧
      ∀ input,Traversal (g.label node).index (g.label node).sort p q input input := by
  cases source with
  | appCtx => cases outgoing
  | lamCtx => cases outgoing
  | lamBind => cases outgoing
  | appFun node q m lab port => exact app_fun_predecessor _ q (congrArg (fun l => l.sort) lab) port
  | appArg node q m lab port => exact app_arg_predecessor _ q (congrArg (fun l => l.sort) lab) port
  | lamBody node q m lab port => exact lam_body_predecessor _ q (congrArg (fun l => l.sort) lab) port

/-- Every designated initial outgoing source is reached by a real root prefix
whose context is unchanged for every input. The source segment is retained as
an overlap endpoint, so it can be joined to an arbitrary supplied source path. -/
theorem encode_source_identity_prefix (t : Term) (level : Nat)
    (e : Endpoint (encode level t).net) (role : ProperRole) (m : Nat)
    (source : AtProperRole (encode level t).net (.inl ()) e role m) (outgoing : role.outgoing) :
    ∃ pre : List (Endpoint (encode level t).net),
      (pre++[e]).head?=some (.inr (.inl (.inl ()))) ∧
      ∀ input,Labelling (encode level t).net (pre++[e]) input input := by
  cases e with
  | inr e =>
    cases source
    exact ⟨[],rfl,fun input => .single _ input⟩
  | inl nodePort =>
    obtain ⟨node,q⟩ := nodePort
    obtain ⟨p,context,turn⟩ := source_turn source outgoing
    obtain ⟨pre,rooted,last,labels⟩ := encode_context_port_identity t level node p context
    refine ⟨pre,?_,?_⟩
    · rw [List.head?_append,rooted]; rfl
    · intro input
      apply (labels input).append_seam (.single (.inl ⟨node,q⟩) input)
      intro left right leftEnd rightStart
      have sameLeft : left=(encode level t).net.wire (.inl ⟨node,p⟩) := Option.some.inj (leftEnd.symm.trans last)
      have sameRight : right=.inl ⟨node,q⟩ := (Option.some.inj rightStart).symm
      rw [sameLeft,sameRight,Pairing.involutive]
      exact .node node p q (turn input)
end Lamping.AG

namespace Lamping.AG
open Graph Lambda
/-- Arbitrary-input existence on the given physical path from an actual
initial outgoing source. Join its real identity root prefix, relabel the
rooted path, then split back at the same source occurrence. -/
theorem encode_source_relabel (t : Term) (level : Nat)
    (es : List (Endpoint (encode level t).net)) (e : Endpoint (encode level t).net)
    (role : ProperRole) (m : Nat)
    (source : AtProperRole (encode level t).net (.inl ()) e role m) (outgoing : role.outgoing)
    (head : es.head?=some e) (labels : Labelling (encode level t).net es a b) :
    ∀ input,∃ output,Labelling (encode level t).net es input output := by
  obtain ⟨pre,rooted,prefixLabels⟩ := encode_source_identity_prefix t level e role m source outgoing
  cases es with
  | nil => cases head
  | cons first tail =>
    have same : first=e := Option.some.inj head
    subst first
    have whole := (prefixLabels a).join labels
    have wholeRoot : (pre++e::tail).head?=some (.inr (.inl (.inl ()))) := by
      cases pre <;> exact rooted
    intro input
    obtain ⟨output,wholeLabels⟩ := encode_root_relabel_input t level (pre++e::tail) wholeRoot ⟨a,b,whole⟩ input
    obtain ⟨middle,first,last⟩ := wholeLabels.split_segment
    have equal : middle=input := first.output_unique (prefixLabels input)
    subst middle
    exact ⟨output,last⟩
end Lamping.AG
