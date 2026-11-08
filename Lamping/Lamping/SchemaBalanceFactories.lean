import Lamping.Lamping.LevelBalance
namespace Lamping.AG
open Graph

def wires_balance {A B : Type} [FiniteNames A] [FiniteNames B] (route : Bij A B)
    (boundary : A⊕B → Int) (same : ∀ a,boundary (.inl a)=boundary (.inr (route a))) :
    LevelBalance (wires A B route) boundary where
  nodes := Empty.elim
  vertices := Empty.elim
  wiring := by
    rintro (⟨node,p⟩ | ((a|b) | ⟨w,d⟩))
    · exact nomatch node
    · exact (same a).symm
    · change boundary (.inl (route.invFun b))=boundary (.inr b)
      simpa only [route.right_inv] using same (route.invFun b)
    · exact nomatch w

def fanRight_balance (f : Op) (i j : Nat) (active passive : Int) (boundary : Bool⊕Aux f → Int)
    (left : ∀ b,boundary (.inl b)=active)
    (right : ∀ a,boundary (.inr a)=portDepth j (.op f) passive (.inr a))
    (principal : portDepth j (.op f) passive (.inl ())=active) :
    LevelBalance (fanRight f i j) boundary where
  nodes := Sum.elim (fun _ => passive) (fun a => portDepth j (.op f) passive (.inr a))
  vertices := Empty.elim
  wiring := by
    rintro (⟨b|a,p⟩ | ((b|a) | ⟨w,d⟩))
    · cases p with
      | inl u => cases u; exact (left b).trans principal.symm
      | inr a => rfl
    · cases p with
      | inl u => cases u; exact right a
      | inr b => rfl
    · exact principal.trans (left b).symm
    · exact (right a).symm
    · exact nomatch w

theorem portDepth_shift_down (f : Op) (j : Nat) (positive : 0<j) (base : Int) (p : Port (.op f)) :
    portDepth (j-1) (.op f) (base-1) p=portDepth j (.op f) base p-1 := by
  cases f <;> cases p with
  | inl u => simp only [portDepth] <;> omega
  | inr a => cases a <;> simp only [portDepth] <;> omega

theorem portDepth_shift_up (f : Op) (j : Nat) (base : Int) (p : Port (.op f)) :
    portDepth (j+1) (.op f) (base+1) p=portDepth j (.op f) base p+1 := by
  cases f <;> cases p with
  | inl u => simp only [portDepth] <;> omega
  | inr a => cases a <;> simp only [portDepth] <;> omega

def croRight_balance (f : Op) (i j : Nat) (positive : 0<j) (active passive : Int)
    (boundary : Unit⊕Aux f → Int)
    (left : boundary (.inl ())=active)
    (right : ∀ a,boundary (.inr a)=portDepth j (.op f) passive (.inr a))
    (principal : portDepth j (.op f) passive (.inl ())=active+1) :
    LevelBalance (unaryRight .cro f i j) boundary where
  nodes := Sum.elim (fun _ => passive-1) (fun a => portDepth j (.op f) passive (.inr a)-1)
  vertices := Empty.elim
  wiring := by
    rintro (⟨u|a,p⟩ | ((u|a) | ⟨w,d⟩))
    · cases u
      cases p with
      | inl u =>
        cases u
        change boundary (.inl ())=portDepth (j-1) (.op f) (passive-1) (.inl ())
        rw [portDepth_shift_down f j positive,principal,left]
        omega
      | inr a =>
        change portDepth j (.op f) passive (.inr a)-1=portDepth (j-1) (.op f) (passive-1) (.inr a)
        exact (portDepth_shift_down f j positive passive (.inr a)).symm
    · cases p with
      | inl u =>
        cases u
        change boundary (.inr a)=(portDepth j (.op f) passive (.inr a)-1)+1
        rw [right]
        omega
      | inr u =>
        change portDepth (j-1) (.op f) (passive-1) (.inr a)=portDepth j (.op f) passive (.inr a)-1
        exact portDepth_shift_down f j positive passive (.inr a)
    · cases u
      change portDepth (j-1) (.op f) (passive-1) (.inl ())=boundary (.inl ())
      rw [portDepth_shift_down f j positive,principal,left]
      omega
    · change (portDepth j (.op f) passive (.inr a)-1)+1=boundary (.inr a)
      rw [right]
      omega
    · exact nomatch w

def braRight_balance (f : Op) (i j : Nat) (active passive : Int) (boundary : Unit⊕Aux f → Int)
    (left : boundary (.inl ())=active+1)
    (right : ∀ a,boundary (.inr a)=portDepth j (.op f) passive (.inr a))
    (principal : portDepth j (.op f) passive (.inl ())=active) :
    LevelBalance (unaryRight .bra f i j) boundary where
  nodes := Sum.elim (fun _ => passive+1) (fun a => portDepth j (.op f) passive (.inr a))
  vertices := Empty.elim
  wiring := by
    rintro (⟨u|a,p⟩ | ((u|a) | ⟨w,d⟩))
    · cases u
      cases p with
      | inl u =>
        cases u
        change boundary (.inl ())=portDepth (j+1) (.op f) (passive+1) (.inl ())
        rw [portDepth_shift_up,principal,left]
      | inr a =>
        change portDepth j (.op f) passive (.inr a)+1=portDepth (j+1) (.op f) (passive+1) (.inr a)
        exact (portDepth_shift_up f j passive (.inr a)).symm
    · cases p with
      | inl u => cases u; exact right a
      | inr u => exact portDepth_shift_up f j passive (.inr a)
    · cases u
      change portDepth (j+1) (.op f) (passive+1) (.inl ())=boundary (.inl ())
      rw [portDepth_shift_up,principal,left]
    · exact (right a).symm
    · exact nomatch w
end Lamping.AG
