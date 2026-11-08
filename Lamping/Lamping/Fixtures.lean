import Lamping.Lamping.Encoding
import Lamping.Lamping.PathRewrite
namespace Lamping.AG
open Graph Lambda
abbrev identity : Term := .lam (.var 0)
abbrev identityApp : Term := .app identity identity
abbrev identityAppNet := (encode 0 identityApp).net
abbrev IdentityW := (Empty ⊕ Empty) ⊕ Boundary (.var 0)
abbrev BetaKept := Unit ⊕ (Unit ⊕ Unit)
abbrev BetaW := (IdentityW ⊕ IdentityW) ⊕ Unit
def betaKeptLabels : BetaKept → Label signature :=
  Sum.elim (fun _ => label .cro 0) (Sum.elim (fun _ => label .lam 1) (fun _ => label .cro 1))
def noIdentityFV (x : FV identity) : False := by
  have h := x.property
  change x.val+1 = 0 at h
  omega
abbrev BetaLabel := ambientLabel (.beta 0) betaKeptLabels
abbrev BetaEnd := End signature (BetaKept ⊕ (Unit ⊕ Unit)) (Boundary identityApp) (BetaW ⊕ Unit) BetaLabel

/-- A literal named-end bijection of the recursively encoded graph, not a hand-built substitute. -/
def betaEncodingEnds : Bij (End signature (AppNodes identity identity ⊕ ((Unit ⊕ Unit) ⊕ (Unit ⊕ Unit))) (Boundary identityApp) ((Empty ⊕ (IdentityW ⊕ IdentityW)) ⊕ (Boundary identity ⊕ Boundary identity)) identityAppNet.label) BetaEnd where
  toFun
    | .inl ⟨.inl (.inl _),p⟩ => .inl ⟨.inr (.inl ()),p⟩
    | .inl ⟨.inl (.inr (.inl x)),_⟩ => False.elim (noIdentityFV x)
    | .inl ⟨.inl (.inr (.inr x)),_⟩ => False.elim (noIdentityFV x.val)
    | .inl ⟨.inr (.inl (.inl _)),p⟩ => .inl ⟨.inr (.inr ()),p⟩
    | .inl ⟨.inr (.inl (.inr _)),p⟩ => .inl ⟨.inl (.inl ()),p⟩
    | .inl ⟨.inr (.inr (.inl _)),p⟩ => .inl ⟨.inl (.inr (.inl ())),p⟩
    | .inl ⟨.inr (.inr (.inr _)),p⟩ => .inl ⟨.inl (.inr (.inr ())),p⟩
    | .inr (.inl b) => .inr (.inl b)
    | .inr (.inr (.inl (.inl e),_)) => nomatch e
    | .inr (.inr (.inl (.inr w),d)) => .inr (.inr (.inl (.inl w),d))
    | .inr (.inr (.inr (.inl (.inl _)),d)) => .inr (.inr (.inr (),d))
    | .inr (.inr (.inr (.inl (.inr x)),_)) => False.elim (noIdentityFV x)
    | .inr (.inr (.inr (.inr (.inl _)),d)) => .inr (.inr (.inl (.inr ()),d))
    | .inr (.inr (.inr (.inr (.inr x)),_)) => False.elim (noIdentityFV x)
  invFun
    | .inl ⟨.inr (.inl _),p⟩ => .inl ⟨.inl (.inl ()),p⟩
    | .inl ⟨.inr (.inr _),p⟩ => .inl ⟨.inr (.inl (.inl ())),p⟩
    | .inl ⟨.inl (.inl _),p⟩ => .inl ⟨.inr (.inl (.inr ())),p⟩
    | .inl ⟨.inl (.inr (.inl _)),p⟩ => .inl ⟨.inr (.inr (.inl ())),p⟩
    | .inl ⟨.inl (.inr (.inr _)),p⟩ => .inl ⟨.inr (.inr (.inr ())),p⟩
    | .inr (.inl b) => .inr (.inl b)
    | .inr (.inr (.inl (.inl w),d)) => .inr (.inr (.inl (.inr w),d))
    | .inr (.inr (.inl (.inr _),d)) => .inr (.inr (.inr (.inr (.inl ())),d))
    | .inr (.inr (.inr _,d)) => .inr (.inr (.inr (.inl (.inl ())),d))
  left_inv := by
    rintro (⟨(u | (x | x)) | ((v | w) | (y | z)),p⟩ | (b | ⟨(e | w) | ((v | x) | (y | z)),d⟩))
    · cases u; rfl
    · exact False.elim (noIdentityFV x)
    · exact False.elim (noIdentityFV x.val)
    · cases v; rfl
    · cases w; rfl
    · cases y; rfl
    · cases z; rfl
    · rfl
    · exact nomatch e
    · rfl
    · cases v; rfl
    · exact False.elim (noIdentityFV x)
    · cases y; rfl
    · exact False.elim (noIdentityFV z)
  right_inv := by
    rintro (⟨(u | (v | w)) | (x | y),p⟩ | (b | ⟨(w | u) | v,d⟩))
    · cases u; rfl
    · cases v; rfl
    · cases w; rfl
    · cases x; rfl
    · cases y; rfl
    · rfl
    · rfl
    · cases u; rfl
    · cases v; rfl

def actualBetaNet : Net signature (BetaKept ⊕ (Unit ⊕ Unit)) (Boundary identityApp) (BetaW ⊕ Unit) :=
  ⟨BetaLabel,identityAppNet.wire.rename betaEncodingEnds⟩

/-- The selected principal wire has exactly one transparent vertex. -/
def oneWireInternal : Pairing (Bool ⊕ (Unit × Bool)) where
  mate
    | .inl b => .inr ((),b)
    | .inr (_,b) => .inl b
  involutive := by rintro (b | ⟨u,b⟩); rfl; cases u; rfl
  fixedPointFree := by rintro (b | ub) h <;> cases h

theorem oneWireConnected : ∀ x, InternalReach oneWireInternal (.inl false) x := by
  intro x
  have h0 : InternalReach oneWireInternal (.inl false) (.inr ((),false)) := .segment _
  have h1 : InternalReach oneWireInternal (.inl false) (.inr ((),true)) := .trans h0 (.vertex () false)
  have h2 : InternalReach oneWireInternal (.inl false) (.inl true) := .trans h1 (.segment _)
  rcases x with b | ⟨u,b⟩
  · cases b; exact .refl _; exact h2
  · cases u; cases b; exact h0; exact h1

def actualBetaSite : PathSite (.beta 0) betaKeptLabels (B := Boundary identityApp) (W := BetaW) (V := Unit) where
  wire := actualBetaNet.wire
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨u,b⟩)
    · cases b <;> rfl
    · cases u; cases b <;> rfl

def actualBetaReduced := actualBetaSite.reduce
abbrev ContinuationW := Unit ⊕ (IdentityW ⊕ Bool)
abbrev ContinuationV := Bool × Bool
def continuationKept : Unit → Label signature := fun _ => label .cro 1
abbrev continuationSchema : Schema := .croAction .lam 0 1 (by decide)
abbrev ContinuationLabel := ambientLabel continuationSchema continuationKept
abbrev ContinuationEnd := End signature (Unit ⊕ (Unit ⊕ Unit)) (Boundary identityApp)
  (ContinuationW ⊕ ContinuationV) ContinuationLabel

def continuationVertices : Bij ((BetaW ⊕ Empty) ⊕ (Bool ⊕ Bool)) (ContinuationW ⊕ ContinuationV) where
  toFun
    | .inl (.inl (.inl (.inl (.inl e)))) => nomatch e
    | .inl (.inl (.inl (.inl (.inr (.inl _))))) => .inl (.inl ())
    | .inl (.inl (.inl (.inl (.inr (.inr _))))) => .inr (false,false)
    | .inl (.inl (.inl (.inr w))) => .inl (.inr (.inl w))
    | .inl (.inl (.inr _)) => .inr (true,true)
    | .inl (.inr e) => nomatch e
    | .inr (.inl false) => .inl (.inr (.inr false))
    | .inr (.inl true) => .inr (true,false)
    | .inr (.inr false) => .inr (false,true)
    | .inr (.inr true) => .inl (.inr (.inr true))
  invFun
    | .inl (.inl _) => .inl (.inl (.inl (.inl (.inr (.inl ())))))
    | .inl (.inr (.inl w)) => .inl (.inl (.inl (.inr w)))
    | .inl (.inr (.inr false)) => .inr (.inl false)
    | .inl (.inr (.inr true)) => .inr (.inr true)
    | .inr (false,false) => .inl (.inl (.inl (.inl (.inr (.inr ⟨0,rfl⟩)))))
    | .inr (false,true) => .inr (.inr false)
    | .inr (true,false) => .inr (.inl true)
    | .inr (true,true) => .inl (.inl (.inr ()))
  left_inv := by
    rintro (((((e | (u | ⟨k,h⟩)) | w) | v) | e) | (q | q))
    · exact nomatch e
    · cases u; rfl
    · change k = 0 at h; subst k; rfl
    · rfl
    · cases v; rfl
    · exact nomatch e
    · cases q <;> rfl
    · cases q <;> rfl
  right_inv := by
    rintro ((u | (w | q)) | ⟨q,r⟩)
    · cases u; rfl
    · rfl
    · cases q <;> rfl
    · cases q <;> cases r <;> rfl

def continuationEnds : Bij
    (End signature (BetaKept ⊕ Empty) (Boundary identityApp)
      ((BetaW ⊕ Empty) ⊕ (Bool ⊕ Bool)) actualBetaReduced.label) ContinuationEnd where
  toFun
    | .inl ⟨.inl (.inl _),p⟩ => .inl ⟨.inr (.inl ()),p⟩
    | .inl ⟨.inl (.inr (.inl _)),p⟩ => .inl ⟨.inr (.inr ()),p⟩
    | .inl ⟨.inl (.inr (.inr _)),p⟩ => .inl ⟨.inl (),p⟩
    | .inl ⟨.inr e,_⟩ => nomatch e
    | .inr (.inl b) => .inr (.inl b)
    | .inr (.inr (w,d)) => .inr (.inr (continuationVertices w,d))
  invFun
    | .inl ⟨.inr (.inl _),p⟩ => .inl ⟨.inl (.inl ()),p⟩
    | .inl ⟨.inr (.inr _),p⟩ => .inl ⟨.inl (.inr (.inl ())),p⟩
    | .inl ⟨.inl _,p⟩ => .inl ⟨.inl (.inr (.inr ())),p⟩
    | .inr (.inl b) => .inr (.inl b)
    | .inr (.inr (w,d)) => .inr (.inr (continuationVertices.invFun w,d))
  left_inv := by
    rintro (⟨((u | (v | w)) | e),p⟩ | (b | ⟨w,d⟩))
    · cases u; rfl
    · cases v; rfl
    · cases w; rfl
    · exact nomatch e
    · rfl
    · simp [continuationVertices.left_inv]
  right_inv := by
    rintro (⟨u | (v | w),p⟩ | (b | ⟨w,d⟩))
    · cases u; rfl
    · cases v; rfl
    · cases w; rfl
    · rfl
    · simp [continuationVertices.right_inv]
def continuationInternal : Pairing (Bool ⊕ (ContinuationV × Bool)) where
  mate
    | .inl false => .inr ((false,false),true)
    | .inl true => .inr ((true,true),true)
    | .inr ((false,false),true) => .inl false
    | .inr ((false,false),false) => .inr ((false,true),false)
    | .inr ((false,true),false) => .inr ((false,false),false)
    | .inr ((false,true),true) => .inr ((true,false),true)
    | .inr ((true,false),true) => .inr ((false,true),true)
    | .inr ((true,false),false) => .inr ((true,true),false)
    | .inr ((true,true),false) => .inr ((true,false),false)
    | .inr ((true,true),true) => .inl true
  involutive := by rintro (b | ⟨⟨a,b⟩,d⟩); cases b <;> rfl; cases a <;> cases b <;> cases d <;> rfl
  fixedPointFree := by
    rintro (b | ⟨⟨a,b⟩,d⟩)
    · cases b <;> (intro h; cases h)
    · cases a <;> cases b <;> cases d <;> (intro h; cases h)

theorem continuationConnected : ∀ x, InternalReach continuationInternal (.inl false) x := by
  have h0 : InternalReach continuationInternal (.inl false) (.inr ((false,false),true)) := .segment _
  have h1 : InternalReach continuationInternal (.inl false) (.inr ((false,false),false)) := .trans h0 (.vertex _ true)
  have h2 : InternalReach continuationInternal (.inl false) (.inr ((false,true),false)) := .trans h1 (.segment _)
  have h3 : InternalReach continuationInternal (.inl false) (.inr ((false,true),true)) := .trans h2 (.vertex _ false)
  have h4 : InternalReach continuationInternal (.inl false) (.inr ((true,false),true)) := .trans h3 (.segment _)
  have h5 : InternalReach continuationInternal (.inl false) (.inr ((true,false),false)) := .trans h4 (.vertex _ true)
  have h6 : InternalReach continuationInternal (.inl false) (.inr ((true,true),false)) := .trans h5 (.segment _)
  have h7 : InternalReach continuationInternal (.inl false) (.inr ((true,true),true)) := .trans h6 (.vertex _ false)
  have h8 : InternalReach continuationInternal (.inl false) (.inl true) := .trans h7 (.segment _)
  rintro (b | ⟨⟨a,b⟩,d⟩)
  · cases b; exact .refl _; exact h8
  · cases a <;> cases b <;> cases d
    exact h1; exact h0; exact h2; exact h3; exact h5; exact h4; exact h6; exact h7

def actualContinuationSite : PathSite continuationSchema continuationKept
    (B := Boundary identityApp) (W := ContinuationW) (V := ContinuationV) where
  wire := actualBetaReduced.wire.rename continuationEnds
  internal := continuationInternal
  connected := continuationConnected
  wiring := by
    rintro (b | ⟨⟨a,b⟩,d⟩)
    · cases b <;> rfl
    · cases a <;> cases b <;> cases d <;> rfl

def actualControlReduced := actualContinuationSite.reduce

theorem beta_encoding_wiring (e) :
    betaEncodingEnds (identityAppNet.wire e) = actualBetaNet.wire (betaEncodingEnds e) :=
  (Pairing.rename_apply identityAppNet.wire betaEncodingEnds e).symm

theorem continuation_wiring (e) :
    continuationEnds (actualBetaReduced.wire e) = actualContinuationSite.net.wire (continuationEnds e) :=
  (Pairing.rename_apply actualBetaReduced.wire continuationEnds e).symm

theorem actual_control_passive_level :
    actualControlReduced.label (.inr (.inl ())) = label .lam 0 := rfl

theorem actual_control_active_levels (q : Bool) :
    actualControlReduced.label (.inr (.inr q)) = label .cro 0 := rfl

theorem actual_final_boundary : actualControlReduced.boundaryOrder = [Sum.inl ()] :=
  closed_boundary_order 0 identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩

#print axioms actualBetaSite
#print axioms actualContinuationSite
#print axioms beta_encoding_wiring
#print axioms continuation_wiring
#print axioms actual_control_passive_level
#print axioms actual_final_boundary
end Lamping.AG





