import Lamping.Lamping.System
import Lamping.Lamping.FreeVars
import Lamping.Lamping.Compose
namespace Lamping.AG
open Graph Lambda
abbrev Boundary (t : Term) := Unit ⊕ FV t

def varNet (n k : Nat) : Net signature Unit (Boundary (.var k)) Empty where
  label := fun _ => label .cro n
  wire := {
    mate := fun x => match x with
      | .inl ⟨_,.inl _⟩ => .inr (.inl (.inr ⟨k,rfl⟩))
      | .inl ⟨_,.inr _⟩ => .inr (.inl (.inl ()))
      | .inr (.inl (.inl _)) => .inl ⟨(),.inr ()⟩
      | .inr (.inl (.inr _)) => .inl ⟨(),.inl ()⟩
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨u,p⟩ | ((u | ⟨k',h⟩) | ⟨e,d⟩))
      · cases u; cases p <;> rename_i u <;> cases u <;> rfl
      · cases u; rfl
      · change k' = k at h; subst k'; rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨u,p⟩ | ((u | v) | ⟨e,d⟩))
      · cases p <;> (intro h; cases h)
      · intro h; cases h
      · intro h; cases h
      · exact nomatch e }

/-- The lambda patch retains the body's free inputs except index zero. -/
def lambdaUsed (n : Nat) (b : Term) (used : free b 0) :
    Net signature Unit (Boundary (.lam b) ⊕ Boundary b) Empty where
  label := fun _ => label .lam n
  wire := {
    mate := fun x => match x with
      | .inl ⟨_,.inl _⟩ => .inr (.inl (.inl (.inl ())))
      | .inl ⟨_,.inr false⟩ => .inr (.inl (.inr (.inr ⟨0,used⟩)))
      | .inl ⟨_,.inr true⟩ => .inr (.inl (.inr (.inl ())))
      | .inr (.inl (.inl (.inl _))) => .inl ⟨(),.inl ()⟩
      | .inr (.inl (.inl (.inr ⟨k,h⟩))) => .inr (.inl (.inr (.inr ⟨k+1,h⟩)))
      | .inr (.inl (.inr (.inl _))) => .inl ⟨(),.inr true⟩
      | .inr (.inl (.inr (.inr ⟨0,_⟩))) => .inl ⟨(),.inr false⟩
      | .inr (.inl (.inr (.inr ⟨k+1,h⟩))) => .inr (.inl (.inl (.inr ⟨k,h⟩)))
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨u,p⟩ | (((u | ⟨k,h⟩) | (v | ⟨k',h'⟩)) | ⟨e,d⟩))
      · cases u; cases p with | inl u => cases u; rfl | inr q => cases q <;> rfl
      · cases u; rfl
      · rfl
      · cases v; rfl
      · cases k' <;> rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨u,p⟩ | (((u | v) | (w | ⟨k,h⟩)) | ⟨e,d⟩))
      · cases p with | inl u => intro h; cases h | inr q => cases q <;> (intro h; cases h)
      · intro h; cases h
      · intro h; cases h
      · intro h; cases h
      · cases k <;> (intro h; cases h)
      · exact nomatch e }

/-- The unused binding is sealed by a fresh inert Garbage at canonical index zero. -/
def lambdaUnused (n : Nat) (b : Term) (unused : ¬ free b 0) :
    Net signature (Unit ⊕ Unit) (Boundary (.lam b) ⊕ Boundary b) Empty where
  label := Sum.elim (fun _ => label .lam n) (fun _ => garbage)
  wire := {
    mate := fun x => match x with
      | .inl ⟨.inl _,.inl _⟩ => .inr (.inl (.inl (.inl ())))
      | .inl ⟨.inl _,.inr false⟩ => .inl ⟨.inr (),()⟩
      | .inl ⟨.inl _,.inr true⟩ => .inr (.inl (.inr (.inl ())))
      | .inl ⟨.inr _,_⟩ => .inl ⟨.inl (),.inr false⟩
      | .inr (.inl (.inl (.inl _))) => .inl ⟨.inl (),.inl ()⟩
      | .inr (.inl (.inl (.inr ⟨k,h⟩))) => .inr (.inl (.inr (.inr ⟨k+1,h⟩)))
      | .inr (.inl (.inr (.inl _))) => .inl ⟨.inl (),.inr true⟩
      | .inr (.inl (.inr (.inr ⟨0,h⟩))) => False.elim (unused h)
      | .inr (.inl (.inr (.inr ⟨k+1,h⟩))) => .inr (.inl (.inl (.inr ⟨k,h⟩)))
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨u | u,p⟩ | (((u | ⟨k,h⟩) | (v | ⟨k',h'⟩)) | ⟨e,d⟩))
      · cases u; cases p with | inl u => cases u; rfl | inr q => cases q <;> rfl
      · cases u; cases p; rfl
      · cases u; rfl
      · rfl
      · cases v; rfl
      · cases k' with | zero => exact False.elim (unused h') | succ k => rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨u | u,p⟩ | (((u | v) | (w | ⟨k,h⟩)) | ⟨e,d⟩))
      · cases p with | inl u => intro h; cases h | inr q => cases q <;> (intro h; cases h)
      · intro h; cases h
      · intro h; cases h
      · intro h; cases h
      · intro h; cases h
      · cases k with | zero => exact False.elim (unused h) | succ k => intro h; cases h
      · exact nomatch e }
instance finiteSubtype {A : Type} [FiniteNames A] (P : A → Prop) [DecidablePred P] :
    FiniteNames {a // P a} where
  all := ((FiniteNames.all : List A).filter (fun x => decide (P x))).attach.map (fun x => (⟨x.val,by simpa using (List.mem_filter.mp x.property).2⟩ : {a // P a}))
  complete x := by
    apply List.mem_map.mpr
    refine ⟨⟨x.val,List.mem_filter.mpr ⟨FiniteNames.complete _,(by simp only [decide_eq_true_eq]; exact x.property)⟩⟩,List.mem_attach _ _,?_⟩
    exact Subtype.ext rfl
abbrev Shared (f a : Term) := {x : FV a // free f x.val}
abbrev AppNodes (f a : Term) := Unit ⊕ (FV a ⊕ Shared f a)
def appLabels (n : Nat) (f a : Term) : AppNodes f a → Label signature :=
  Sum.elim (fun _ => label .app n) (Sum.elim (fun _ => label .bra n) (fun _ => label .fan n))
abbrev AppEnd (n : Nat) (f a : Term) :=
  End signature (AppNodes f a) (Boundary (.app f a) ⊕ (Boundary f ⊕ Boundary a)) Empty (appLabels n f a)

def appMate (n : Nat) (f a : Term) : AppEnd n f a → AppEnd n f a
  | .inl ⟨.inl _,.inl _⟩ => .inr (.inl (.inr (.inl (.inl ()))))
  | .inl ⟨.inl _,.inr false⟩ => .inr (.inl (.inl (.inl ())))
  | .inl ⟨.inl _,.inr true⟩ => .inr (.inl (.inr (.inr (.inl ()))))
  | .inl ⟨.inr (.inl x),.inl _⟩ =>
    if h : free f x.val then .inl ⟨.inr (.inr ⟨x,h⟩),.inr true⟩
    else .inr (.inl (.inl (.inr ⟨x.val,Or.inr x.property⟩)))
  | .inl ⟨.inr (.inl x),.inr _⟩ => .inr (.inl (.inr (.inr (.inr x))))
  | .inl ⟨.inr (.inr x),.inl _⟩ => .inr (.inl (.inl (.inr ⟨x.val.val,Or.inr x.val.property⟩)))
  | .inl ⟨.inr (.inr x),.inr false⟩ => .inr (.inl (.inr (.inl (.inr ⟨x.val.val,x.property⟩))))
  | .inl ⟨.inr (.inr x),.inr true⟩ => .inl ⟨.inr (.inl x.val),.inl ()⟩
  | .inr (.inl (.inl (.inl _))) => .inl ⟨.inl (),.inr false⟩
  | .inr (.inl (.inl (.inr x))) =>
    if ha : free a x.val then
      if hf : free f x.val then .inl ⟨.inr (.inr ⟨⟨x.val,ha⟩,hf⟩),.inl ()⟩
      else .inl ⟨.inr (.inl ⟨x.val,ha⟩),.inl ()⟩
    else .inr (.inl (.inr (.inl (.inr ⟨x.val, x.property.resolve_right ha⟩))))
  | .inr (.inl (.inr (.inl (.inl _)))) => .inl ⟨.inl (),.inl ()⟩
  | .inr (.inl (.inr (.inl (.inr x)))) =>
    if ha : free a x.val then .inl ⟨.inr (.inr ⟨⟨x.val,ha⟩,x.property⟩),.inr false⟩
    else .inr (.inl (.inl (.inr ⟨x.val,Or.inl x.property⟩)))
  | .inr (.inl (.inr (.inr (.inl _)))) => .inl ⟨.inl (),.inr true⟩
  | .inr (.inl (.inr (.inr (.inr x)))) => .inl ⟨.inr (.inl x),.inr ()⟩
  | .inr (.inr ⟨e,_⟩) => nomatch e

def appPatch (n : Nat) (f a : Term) :
    Net signature (AppNodes f a) (Boundary (.app f a) ⊕ (Boundary f ⊕ Boundary a)) Empty where
  label := appLabels n f a
  wire := {
    mate := appMate n f a
    involutive := by
      rintro (⟨u | (x | x),p⟩ | (((u | x) | ((v | y) | (w | z))) | ⟨e,d⟩))
      · cases u; cases p with | inl u => cases u; rfl | inr q => cases q <;> rfl
      · cases p with
        | inl u => cases u; by_cases h : free f x.val <;> simp [appMate,h,x.property]
        | inr u => cases u; rfl
      · cases p with
        | inl u => cases u; simp [appMate,x.property,x.val.property]
        | inr q => cases q <;> simp [appMate,x.property,x.val.property]
      · cases u; rfl
      · by_cases ha : free a x.val <;> by_cases hf : free f x.val <;> simp [appMate,ha,hf]
      · cases v; rfl
      · by_cases ha : free a y.val <;> simp [appMate,ha]
      · cases w; rfl
      · rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨u | (x | x),p⟩ | (((u | x) | ((v | y) | (w | z))) | ⟨e,d⟩))
      · cases p with | inl u => intro h; cases h | inr q => cases q <;> (intro h; cases h)
      · cases p with
        | inl u => simp only [appMate]; split <;> (intro h; cases h)
        | inr u => intro h; cases h
      · cases p with | inl u => intro h; cases h | inr q => cases q <;> (intro h; cases h)
      · intro h; cases h
      · simp only [appMate]; split; split <;> (intro h; cases h); intro h; cases h
      · intro h; cases h
      · simp only [appMate]; split <;> (intro h; cases h)
      · intro h; cases h
      · intro h; cases h
      · exact nomatch e }

/-- Actual recursive AG98 translation. Each constructor composes explicit matching nets. -/
def encode (n : Nat) : (t : Term) → Fragment (Boundary t)
  | .var k => ⟨Unit,Empty,inferInstance,inferInstance,varNet n k⟩
  | .lam b =>
    let body := encode n b
    if h : free b 0 then
      ⟨Unit ⊕ body.N, (Empty ⊕ body.W) ⊕ Boundary b,inferInstance,inferInstance,
        plug (lambdaUsed n b h) body.net⟩
    else
      ⟨(Unit ⊕ Unit) ⊕ body.N, (Empty ⊕ body.W) ⊕ Boundary b,inferInstance,inferInstance,
        plug (lambdaUnused n b h) body.net⟩
  | .app f a =>
    let fn := encode n f
    let arg := encode (n+1) a
    ⟨AppNodes f a ⊕ (fn.N ⊕ arg.N),
      (Empty ⊕ (fn.W ⊕ arg.W)) ⊕ (Boundary f ⊕ Boundary a),inferInstance,inferInstance,
      plug (appPatch n f a) (unionNet fn.net arg.net)⟩

theorem encode_pairing (n : Nat) (t : Term) (e) :
    (encode n t).net.wire ((encode n t).net.wire e) = e := (encode n t).net.wire.involutive e
/-- Boundary correspondence is the actual free-index subtype, not the ambient scope. -/
theorem encode_boundary (n : Nat) (t : Term) (b : Boundary t) :
    b ∈ (encode n t).net.boundaryOrder := (encode n t).net.boundaryOrder_complete b

theorem closed_boundary_unique (_n : Nat) (t : Term) (h : Closed t) (b : Boundary t) :
    b = Sum.inl () := by
  cases b with
  | inl u => cases u; rfl
  | inr x => exact False.elim (closed_fv_empty h x)


theorem closed_boundary_order (n : Nat) (t : Term) (h : Closed t) :
    (encode n t).net.boundaryOrder = [Sum.inl ()] := by
  have hd := (encode n t).net.boundaryOrder_nodup
  have hm := (encode n t).net.boundaryOrder_complete (Sum.inl ())
  cases he : (encode n t).net.boundaryOrder with
  | nil => simp [he] at hm
  | cons x xs =>
    have hx := closed_boundary_unique n t h x
    subst x
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hy := closed_boundary_unique n t h y
      subst y
      simp [he] at hd

/-- Garbage's representation-level Nat field is canonically zero in every encoded graph. -/
theorem encode_garbage_zero (t : Term) (n : Nat) : ∀ v,
    ((encode n t).net.label v).sort = .garbage → ((encode n t).net.label v).index = 0 := by
  induction t generalizing n with
  | var k => intro v h; cases h
  | lam b ih =>
    dsimp only [encode]
    by_cases used : free b 0
    · rw [dif_pos used]
      rintro (u | v) h
      · cases h
      · exact ih n v h
    · rw [dif_neg used]
      rintro ((u | u) | v) h
      · cases h
      · rfl
      · exact ih n v h
  | app f a hf ha =>
    simp only [encode]
    rintro ((u | (x | x)) | (v | w)) h
    · cases h
    · cases h
    · cases h
    · exact hf n v h
    · exact ha (n+1) w h
end Lamping.AG








