import Lamping.Graph.Rewrite
namespace Lamping.AG
open Graph
inductive Op where
  | app | lam | fan | cro | bra
  deriving DecidableEq, Repr

def Aux : Op → Type
  | .app | .lam | .fan => Bool
  | .cro | .bra => Unit
instance (f : Op) : FiniteNames (Aux f) := by cases f <;> simp only [Aux] <;> infer_instance
instance (f : Op) : DecidableEq (Aux f) := by cases f <;> simp only [Aux] <;> infer_instance
inductive Kind where
  | op : Op → Kind
  | garbage
  deriving DecidableEq, Repr

def Port : Kind → Type
  | .op f => Unit ⊕ Aux f
  | .garbage => Unit
instance (k : Kind) : FiniteNames (Port k) := by cases k <;> simp only [Port] <;> infer_instance

def signature : Signature where
  Kind := Kind
  Port := Port
  finitePort := inferInstance
  principal := fun k => match k with
    | .op _ => some (.inl ())
    | .garbage => none

def label (f : Op) (i : Nat) : Label signature := ⟨.op f,i⟩
def garbage : Label signature := ⟨.garbage,0⟩
/-- Auxiliary false/true means ctx/arg, bind/body, and o/star respectively. -/
def appCtx : Port (.op .app) := .inr false
def appArg : Port (.op .app) := .inr true
def lamBind : Port (.op .lam) := .inr false
def lamBody : Port (.op .lam) := .inr true
def fanO : Port (.op .fan) := .inr false
def fanStar : Port (.op .fan) := .inr true

/-- A principal pair with every named auxiliary endpoint exposed. -/
def leftNet (f g : Op) (i j : Nat) :
    Net signature (Unit ⊕ Unit) (Aux f ⊕ Aux g) Empty where
  label := Sum.elim (fun _ => label f i) (fun _ => label g j)
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl _, .inl _⟩ => .inl ⟨.inr (), .inl ()⟩
      | .inl ⟨.inr _, .inl _⟩ => .inl ⟨.inl (), .inl ()⟩
      | .inl ⟨.inl _, .inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr _, .inr a⟩ => .inr (.inl (.inr a))
      | .inr (.inl (.inl a)) => .inl ⟨.inl (), .inr a⟩
      | .inr (.inl (.inr a)) => .inl ⟨.inr (), .inr a⟩
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨u | u, p⟩ | ((a | a) | ⟨e,d⟩))
      · cases u; cases p <;> rfl
      · cases u; cases p <;> rfl
      · rfl
      · rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨u | u, p⟩ | ((a | a) | ⟨e,d⟩))
      · cases p <;> (intro h; cases h)
      · cases p <;> (intro h; cases h)
      · intro h; cases h
      · intro h; cases h
      · exact nomatch e }

def wires (A B : Type) [FiniteNames A] [FiniteNames B] (e : Bij A B) :
    Net signature Empty (A ⊕ B) Empty where
  label := Empty.elim
  wire := {
    mate := fun x => match x with
      | .inl ⟨e,_⟩ => nomatch e
      | .inr (.inl (.inl a)) => .inr (.inl (.inr (e a)))
      | .inr (.inl (.inr b)) => .inr (.inl (.inl (e.invFun b)))
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨x,p⟩ | ((a | b) | ⟨x,d⟩))
      · exact nomatch x
      · simp [e.left_inv]
      · simp [e.right_inv]
      · exact nomatch x
    fixedPointFree := by
      rintro (⟨x,p⟩ | ((a | b) | ⟨x,d⟩))
      · exact nomatch x
      · intro h; cases h
      · intro h; cases h
      · exact nomatch x }

def boolFlip : Bij Bool Bool := ⟨not,not,by intro b; cases b <;> rfl,by intro b; cases b <;> rfl⟩

/-- Fan action: false/true copy is the o/star copy; one fresh fan per passive auxiliary. -/
def fanRight (f : Op) (i j : Nat) :
    Net signature (Bool ⊕ Aux f) (Bool ⊕ Aux f) Empty where
  label := Sum.elim (fun _ => label f j) (fun _ => label .fan i)
  wire := {
    mate := fun x => match x with
      | .inl ⟨.inl b,.inl _⟩ => .inr (.inl (.inl b))
      | .inl ⟨.inl b,.inr a⟩ => .inl ⟨.inr a,.inr b⟩
      | .inl ⟨.inr a,.inl _⟩ => .inr (.inl (.inr a))
      | .inl ⟨.inr a,.inr b⟩ => .inl ⟨.inl b,.inr a⟩
      | .inr (.inl (.inl b)) => .inl ⟨.inl b,.inl ()⟩
      | .inr (.inl (.inr a)) => .inl ⟨.inr a,.inl ()⟩
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨b | a,p⟩ | ((b | a) | ⟨e,d⟩))
      · cases p with | inl u => cases u; rfl | inr a => rfl
      · cases p with | inl u => cases u; rfl | inr b => rfl
      · rfl
      · rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨b | a,p⟩ | ((b | a) | ⟨e,d⟩))
      · cases p <;> (intro h; cases h)
      · cases p <;> (intro h; cases h)
      · intro h; cases h
      · intro h; cases h
      · exact nomatch e }

inductive Unary where | cro | bra deriving DecidableEq, Repr
def Unary.op : Unary → Op | .cro => .cro | .bra => .bra
def Unary.shift : Unary → Nat → Nat | .cro, j => j-1 | .bra,j => j+1
/-- Unary action preserves each auxiliary position, changing only the passive level. -/
def unaryRightCore (c f : Op) (a : Bij Unit (Aux c)) (i k : Nat) :
    Net signature (Unit ⊕ Aux f) (Unit ⊕ Aux f) Empty where
  label := Sum.elim (fun _ => label f k) (fun _ => label c i)
  wire := {
    mate := fun x => match x with
      | .inl ⟨.inl _,.inl _⟩ => .inr (.inl (.inl ()))
      | .inl ⟨.inl _,.inr q⟩ => .inl ⟨.inr q,.inr (a ())⟩
      | .inl ⟨.inr q,.inl _⟩ => .inr (.inl (.inr q))
      | .inl ⟨.inr q,.inr _⟩ => .inl ⟨.inl (),.inr q⟩
      | .inr (.inl (.inl _)) => .inl ⟨.inl (),.inl ()⟩
      | .inr (.inl (.inr q)) => .inl ⟨.inr q,.inl ()⟩
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨u | q,p⟩ | ((u | q) | ⟨e,d⟩))
      · cases u; cases p with | inl u => cases u; rfl | inr q => rfl
      · cases p with
        | inl u => cases u; rfl
        | inr v =>
          have h : a () = v := by have := a.right_inv v; cases a.invFun v; exact this
          simp only [h]
      · cases u; rfl
      · rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨u | q,p⟩ | ((u | q) | ⟨e,d⟩))
      · cases p <;> (intro h; cases h)
      · cases p <;> (intro h; cases h)
      · intro h; cases h
      · intro h; cases h
      · exact nomatch e }

def unaryRight (u : Unary) (f : Op) (i j : Nat) :
    Net signature (Unit ⊕ Aux f) (Unit ⊕ Aux f) Empty :=
  match u with
  | .cro => unaryRightCore .cro f (Bij.refl _) i (j-1)
  | .bra => unaryRightCore .bra f (Bij.refl _) i (j+1)
/-- Exactly seven schemas; action constructors carry the strict source side condition. -/
inductive Schema where
  | beta (i : Nat)
  | fanCancel (i : Nat)
  | croCancel (i : Nat)
  | braCancel (i : Nat)
  | fanAction (f : Op) (i j : Nat) (lt : i < j)
  | croAction (f : Op) (i j : Nat) (lt : i < j)
  | braAction (f : Op) (i j : Nat) (lt : i < j)

def Schema.active : Schema → Op
  | .beta _ => .app
  | .fanCancel _ | .fanAction .. => .fan
  | .croCancel _ | .croAction .. => .cro
  | .braCancel _ | .braAction .. => .bra
def Schema.passive : Schema → Op
  | .beta _ => .lam
  | .fanCancel _ => .fan
  | .croCancel _ => .cro
  | .braCancel _ => .bra
  | .fanAction f .. | .croAction f .. | .braAction f .. => f
def Schema.low : Schema → Nat
  | .beta i | .fanCancel i | .croCancel i | .braCancel i => i
  | .fanAction _ i .. | .croAction _ i .. | .braAction _ i .. => i
def Schema.high : Schema → Nat
  | .beta i | .fanCancel i | .croCancel i | .braCancel i => i
  | .fanAction _ _ j _ | .croAction _ _ j _ | .braAction _ _ j _ => j
abbrev Schema.Frontier (s : Schema) := Aux s.active ⊕ Aux s.passive
def Schema.left (s : Schema) := leftNet s.active s.passive s.low s.high

structure Fragment (B : Type) [FiniteNames B] where
  N : Type
  W : Type
  finiteN : FiniteNames N
  finiteW : FiniteNames W
  net : @Net signature N B W finiteN inferInstance finiteW
attribute [instance] Fragment.finiteN Fragment.finiteW

def Schema.right (s : Schema) : Fragment s.Frontier :=
  match s with
  | .beta _ => ⟨Empty,Empty,inferInstance,inferInstance,wires Bool Bool boolFlip⟩
  | .fanCancel _ => ⟨Empty,Empty,inferInstance,inferInstance,wires Bool Bool (Bij.refl _)⟩
  | .croCancel _ | .braCancel _ => ⟨Empty,Empty,inferInstance,inferInstance,wires Unit Unit (Bij.refl _)⟩
  | .fanAction f i j _ => ⟨Bool ⊕ Aux f,Empty,inferInstance,inferInstance,fanRight f i j⟩
  | .croAction f i j _ => ⟨Unit ⊕ Aux f,Empty,inferInstance,inferInstance,unaryRight .cro f i j⟩
  | .braAction f i j _ => ⟨Unit ⊕ Aux f,Empty,inferInstance,inferInstance,unaryRight .bra f i j⟩

theorem cro_action_no_underflow (i j : Nat) (h : i < j) : 0 < j ∧ j-1+1 = j := by
  have hj : 0 < j := Nat.lt_of_le_of_lt (Nat.zero_le i) h
  exact ⟨hj,Nat.sub_add_cancel hj⟩

/-- The two principal ports are internal, and all named auxiliaries are the frontier. -/
def principalPartition (s : Schema) :
    Bij (NodePort signature (Unit ⊕ Unit) s.left.label ⊕ (Empty × Bool))
      (s.Frontier ⊕ Bool) where
  toFun
    | .inl ⟨.inl _,.inl _⟩ => .inr false
    | .inl ⟨.inr _,.inl _⟩ => .inr true
    | .inl ⟨.inl _,.inr a⟩ => .inl (.inl a)
    | .inl ⟨.inr _,.inr a⟩ => .inl (.inr a)
    | .inr ⟨e,_⟩ => nomatch e
  invFun
    | .inr false => .inl ⟨.inl (),.inl ()⟩
    | .inr true => .inl ⟨.inr (),.inl ()⟩
    | .inl (.inl a) => .inl ⟨.inl (),.inr a⟩
    | .inl (.inr a) => .inl ⟨.inr (),.inr a⟩
  left_inv := by
    rintro (⟨u | u,p⟩ | ⟨e,d⟩)
    · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
    · cases u; cases p with | inl u => cases u; rfl | inr a => rfl
    · exact nomatch e
  right_inv := by rintro ((a | a) | b); rfl; rfl; cases b <;> rfl

section Rewrite
variable (s : Schema) {K B W : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W]
variable (kept : K → Label signature)
abbrev ambientLabel := Sum.elim kept s.left.label
/-- Source labels are constructed, rather than supplied as desired target correctness. -/
structure Site where
  wire : Pairing (End signature (K ⊕ (Unit ⊕ Unit)) B (W ⊕ Empty) (ambientLabel s kept))
  principal : wire (.inl ⟨.inr (.inl ()),.inl ()⟩) = .inl ⟨.inr (.inr ()),.inl ()⟩

def Site.net (a : Site s kept (B := B) (W := W)) : Net signature (K ⊕ (Unit ⊕ Unit)) B (W ⊕ Empty) := ⟨ambientLabel s kept,a.wire⟩

theorem Site.internal (a : Site s kept (B := B) (W := W)) (b : Bool) :
    a.wire.rename (fragmentEnd a.net.label (principalPartition s)) (.inr b) = .inr (!b) := by
  cases b
  · change (fragmentEnd _ _) (a.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) = _
    rw [a.principal]; rfl
  · have h := a.wire.involutive (.inl ⟨.inr (.inl ()),.inl ()⟩)
    rw [a.principal] at h
    change (fragmentEnd _ _) (a.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)) = _
    rw [h]; rfl

theorem Site.closed (a : Site s kept (B := B) (W := W)) : ∀ e i,
    a.net.wire.rename (fragmentEnd a.net.label (principalPartition s)) (.inl e) ≠ .inr i := by
  intro e i h
  have hh := congrArg (a.net.wire.rename (fragmentEnd a.net.label (principalPartition s))) h
  rw [Pairing.involutive] at hh
  change Sum.inl e = a.wire.rename (fragmentEnd a.net.label (principalPartition s)) (.inr i) at hh
  rw [a.internal] at hh
  cases hh

/-- The executable AG rewrite is precisely P02 cutFragment followed by plug. -/
def Site.reduce (a : Site s kept (B := B) (W := W)) :=
  replace a.net (principalPartition s) a.closed s.right.net

theorem Site.reduce_pairing (a : Site s kept (B := B) (W := W)) (e) :
    a.reduce.wire (a.reduce.wire e) = e := a.reduce.wire.involutive e

theorem Site.reduce_boundary [DecidableEq B] (a : Site s kept (B := B) (W := W)) :
    a.reduce.boundaryOrder = a.net.boundaryOrder := rfl
end Rewrite
end Lamping.AG




