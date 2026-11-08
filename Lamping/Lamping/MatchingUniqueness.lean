import Lamping.Lamping.MatchingDefinitions
namespace Lamping.AG
open Graph Lambda

/-- All syntax observations determine a de Bruijn term, including binder indices. -/
theorem syntaxShape_ext (t u : Term)
    (h : ∀ p v, subtermAt t p = some v →
      ∃ w, subtermAt u p = some w ∧ syntaxShape v = syntaxShape w) : t = u := by
  induction t generalizing u with
  | var k =>
    obtain ⟨w,hw,hs⟩ := h [] (.var k) rfl
    have hu : u = w := Option.some.inj (by simpa only [subtermAt] using hw)
    subst w
    cases u <;> simp_all [syntaxShape]
  | lam b ih =>
    obtain ⟨w,hw,hs⟩ := h [] (.lam b) rfl
    have hu : u = w := Option.some.inj (by simpa only [subtermAt] using hw)
    subst w
    cases u with
    | var k => cases hs
    | app f a => cases hs
    | lam c =>
      congr 1
      apply ih c
      intro p v hp
      exact h (.body::p) v hp
  | app f a ihf iha =>
    obtain ⟨w,hw,hs⟩ := h [] (.app f a) rfl
    have hu : u = w := Option.some.inj (by simpa only [subtermAt] using hw)
    subst w
    cases u with
    | var k => cases hs
    | lam c => cases hs
    | app g b =>
      have hf : f = g := ihf g (by intro p v hp; exact h (.fn::p) v hp)
      have ha : a = b := iha b (by intro p v hp; exact h (.arg::p) v hp)
      rw [hf,ha]

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Def.3.5.13 determines at most one finite term. No reachability, invariants,
or soundness hypothesis is used in this observation argument. -/
theorem Matches.unique {t u : Term} (ht : Matches g root t) (hu : Matches g root u) : t = u := by
  obtain ⟨f,hf,_⟩ := ht
  obtain ⟨j,hj,_⟩ := hu
  apply syntaxShape_ext t u
  intro p v hp
  let pos : Position t := ⟨p, by simp [hp]⟩
  let es := f.invFun pos
  have hc := hf es
  have hd := hj es
  have hfpos : f es = pos := f.right_inv pos
  rw [hfpos] at hc
  have hpj : (j es).val = p := hd.1.symm.trans hc.1
  obtain ⟨v',hv',ho⟩ := hc.2
  have hv : v' = v := Option.some.inj (hv'.symm.trans hp)
  subst v'
  obtain ⟨w,hw,how⟩ := hd.2
  rw [hpj] at hw
  exact ⟨w,hw,Observes.unique g ho how⟩

/-- Even before invariants are proved, the matching map is forced to be the
proper-port word. Thus two matches cannot hide a different access permutation. -/
theorem Matches.map_forced {t : Term} {f : Bij (RootAccess g root) (Position t)}
    (h : ∀ es, Corresponds g es.val t (f es)) (es : RootAccess g root) :
    (f es).val = accessWord g es.val := (h es).1.symm
end
end Lamping.AG

