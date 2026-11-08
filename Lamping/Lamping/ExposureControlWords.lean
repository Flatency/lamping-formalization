import Lamping.Lamping.ActionCanonicalResidual

namespace Lamping.AG
open Graph
namespace ExposureScheduling

/-- true is auxiliary-to-principal (writer), false is principal-to-auxiliary
(reader). The value is only used on actual labelled paths. -/
def controlPortWord : (kind : Kind) → Port kind → List Bool
  | .op .fan, .inl _ => [true]
  | .op .fan, .inr _ => [false]
  | .op .cro, .inl _ => [true]
  | .op .cro, .inr _ => [false]
  | .op .bra, .inl _ => [true]
  | .op .bra, .inr _ => [false]
  | .op .app, _ => []
  | .op .lam, _ => []
  | .garbage, _ => []

def controlWord {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (es : List (Endpoint g)) : List Bool :=
  es.tail.flatMap fun e => match e with
    | .inl ⟨node,port⟩ => controlPortWord (g.label node).sort port
    | .inr _ => []

/-- Exact original rule-net crossing. No hypothetical residual is an input. -/
theorem left_control_crossing_word (low high : Op) (i j : Nat)
    (lowControl : low=.fan ∨low=.cro ∨low=.bra)
    (highControl : high=.fan ∨high=.cro ∨high=.bra)
    (p : Aux low) (q : Aux high) :
    controlWord (leftNet low high i j) (leftRoute low high i j p q)=[true,false] := by
  rcases lowControl with rfl |rfl |rfl <;>
    rcases highControl with rfl |rfl |rfl <;> rfl

/-- The printed fan RHS exchanges the two control directions. Duplication
of the graph does not duplicate either passage on this exact crossing. -/
theorem fan_control_crossing_word (high : Op) (i j : Nat)
    (control : high=.fan ∨high=.cro ∨high=.bra) (branch : Bool) (q : Aux high) :
    controlWord (fanRight high i j) (fanCrossEdges branch q)=[false,true] := by
  rcases control with rfl |rfl |rfl <;> rfl

/-- Both unary action RHSs have the same direction exchange despite their
opposite changes to the passive index. -/
theorem unary_control_crossing_word (low high : Op) (i k : Nat)
    (lowControl : low=.cro ∨low=.bra)
    (highControl : high=.fan ∨high=.cro ∨high=.bra)
    (one : Bij Unit (Aux low)) (q : Aux high) :
    controlWord (unaryRightCore low high one i k) ([.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩])=[false,true] := by
  rcases lowControl with rfl |rfl <;>
    rcases highControl with rfl |rfl |rfl <;> rfl

/-- Reverse crossings still move a writer-reader peak to reader-writer;
reversing a path also reverses each traversal direction. -/
theorem left_control_reverse_word (low high : Op) (i j : Nat)
    (lowControl : low=.fan ∨low=.cro ∨low=.bra)
    (highControl : high=.fan ∨high=.cro ∨high=.bra)
    (p : Aux low) (q : Aux high) :
    controlWord (leftNet low high i j)
      (reverseEdges (leftRoute low high i j p q))=[true,false] := by
  rcases lowControl with rfl |rfl |rfl <;>
    rcases highControl with rfl |rfl |rfl <;> rfl

theorem fan_control_reverse_word (high : Op) (i j : Nat)
    (control : high=.fan ∨high=.cro ∨high=.bra) (branch : Bool) (q : Aux high) :
    controlWord (fanRight high i j) (reverseEdges (fanCrossEdges branch q))=[false,true] := by
  rcases control with rfl |rfl |rfl <;> rfl

theorem unary_control_reverse_word (low high : Op) (i k : Nat)
    (lowControl : low=.cro ∨low=.bra)
    (highControl : high=.fan ∨high=.cro ∨high=.bra)
    (one : Bij Unit (Aux low)) (q : Aux high) :
    controlWord (unaryRightCore low high one i k)
      (reverseEdges ([.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩]))=[false,true] := by
  rcases lowControl with rfl |rfl <;>
    rcases highControl with rfl |rfl |rfl <;> rfl

/-- An internal control passage cannot use the passive branch of an action
residual: its two ports would both be auxiliary. -/
theorem no_control_passive (op : Op) (i : Nat)
    (control : op=.fan ∨op=.cro ∨op=.bra)
    (p q : Aux op) (a b : Context)
    (turn : Traversal i (.op op) (.inr p) (.inr q) a b) : False := by
  have impossible := turn.aux_aux
  rcases control with rfl |rfl |rfl <;> exact impossible

/-- Actual partial source at the app end, directed from app principal to
control auxiliary. This is not a complete LocalPath between frontiers. -/
theorem initial_source_word (low : Op) (i j : Nat)
    (control : low=.fan ∨low=.cro ∨low=.bra) (p : Aux low) :
    controlWord (leftNet low .app i j)
      [.inl ⟨.inr (),.inl ()⟩,.inl ⟨.inl (),.inr p⟩]=[false] := by
  rcases control with rfl |rfl |rfl <;> rfl

/-- Actual partial source at the lambda end. -/
theorem terminal_source_word (low : Op) (i j : Nat)
    (control : low=.fan ∨low=.cro ∨low=.bra) (p : Aux low) :
    controlWord (leftNet low .lam i j)
      [.inr (.inl (.inl p)),.inl ⟨.inl (),.inl ()⟩]=[true] := by
  rcases control with rfl |rfl |rfl <;> rfl

theorem singleton_word {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (e : Endpoint g) : controlWord g [e]=[] := rfl

/-- The candidate rank is derived from the actual path, never a caller field. -/
def controlCount {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (es : List (Endpoint g)) : Nat := (controlWord g es).length

/-- Counts writer-before-reader pairs, not graph nodes or physical W vertices. -/
def readers : List Bool → Nat
  | [] => 0
  | b::bs => (if b then 0 else 1)+readers bs

def writers : List Bool → Nat
  | [] => 0
  | b::bs => (if b then 1 else 0)+writers bs

def inversions : List Bool → Nat
  | [] => 0
  | b::bs => (if b then readers bs else 0)+inversions bs

private theorem readers_append (xs ys : List Bool) :
    readers (xs++ys)=readers xs+readers ys := by
  induction xs with
  | nil => simp [readers]
  | cons b bs ih => cases b <;> simp [readers,ih,Nat.add_assoc]

private theorem writers_append (xs ys : List Bool) :
    writers (xs++ys)=writers xs+writers ys := by
  induction xs with
  | nil => simp [writers]
  | cons b bs ih => cases b <;> simp [writers,ih,Nat.add_assoc]

private theorem inversions_append (xs ys : List Bool) :
    inversions (xs++ys)=inversions xs+inversions ys+writers xs*readers ys := by
  induction xs with
  | nil => simp [inversions,writers]
  | cons b bs ih =>
    cases b <;> simp [inversions,writers,readers_append,ih,Nat.add_mul] <;> omega

/-- A single actual RHS exchange, once attached to SAME whole-word outside
pieces, strictly lowers inversions without changing the control count. This
lemma does not assert that a graph rewrite alters only one occurrence. -/
theorem exchange_decreases (before after : List Bool) :
    (before++[false,true]++after).length=(before++[true,false]++after).length ∧
    inversions (before++[false,true]++after)<inversions (before++[true,false]++after) := by
  constructor
  · simp
  · simp only [inversions_append,writers_append]
    simp [inversions,readers,writers,Nat.add_mul] <;> omega

/-- Source cancellation removes two control passages, independently of the
number of transparent W subdivisions in its physical principal component. -/
theorem erasure_decreases (before after : List Bool) :
    (before++after).length<(before++[true,false]++after).length := by
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

end ExposureScheduling
end Lamping.AG
