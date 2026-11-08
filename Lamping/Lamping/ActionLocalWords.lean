import Lamping.Lamping.ActionCanonicalWords
namespace Lamping.AG
open Graph Lambda
section Fan
variable {f : Op} {i j : Nat} {lt : i<j}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite (.fanAction f i j lt) kept (B:=B) (W:=W) (V:=V))

/-- All three actual fan canonical local shapes preserve the syntax word,
including the reverse crossing's application-function token. -/
theorem FanCanonicalLocal.word {principal : SiteActionPrincipal site} {rhs old}
    (relation : FanCanonicalLocal site principal rhs old) :
    accessWord site.net old=accessWord (fanRight f i j) rhs := by
  cases relation with
  | cross branch q =>
    rw [principal.crossing_word site (.fan f i j lt)]
    cases f <;> cases q <;> rfl
  | backward branch q =>
    rw [principal.reverse_crossing_word site (.fan f i j lt)]
    cases f <;> cases q <;> rfl
  | passive branch p q =>
    rw [site.passiveCanonical_word p q]
    cases f <;> cases q <;> rfl
end Fan

section Unary
variable {s : Schema} {k : Nat}
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
variable (single : Bij Unit (Aux s.active))

theorem UnaryCanonicalLocal.word {principal : SiteActionPrincipal site} {rhs old}
    (action : IsAction s) (relation : UnaryCanonicalLocal (k:=k) site single principal rhs old) :
    accessWord site.net old=accessWord (unaryRightCore s.active s.passive single s.low k) rhs := by
  cases relation with
  | cross q =>
    rw [principal.crossing_word site action]
    cases action <;> rename_i f i j lt <;> cases f <;> cases q <;> rfl
  | backward q =>
    rw [principal.reverse_crossing_word site action]
    cases action <;> rename_i f i j lt <;> cases f <;> cases q <;> rfl
  | passive p q =>
    rw [site.passiveCanonical_word p q]
    cases action <;> rename_i f i j lt <;> cases f <;> cases q <;> rfl
end Unary

section Actions
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))

/-- Word preservation is proved for the actual chosen canonical source
route, not inferred merely from label equivalence or endpoint kinds. -/
theorem ActionCanonicalLocal.word {principal : SiteActionPrincipal site} {rhs old}
    (relation : ActionCanonicalLocal site principal rhs old) :
    accessWord site.net old=accessWord s.right.net rhs := by
  cases relation with
  | fan relation => exact relation.word _
  | @cro f i j lt actual principal rhs old relation =>
    exact relation.word actual (Bij.refl _) (.cro f i j lt)
  | @bra f i j lt actual principal rhs old relation =>
    exact relation.word actual (Bij.refl _) (.bra f i j lt)
end Actions
end Lamping.AG
