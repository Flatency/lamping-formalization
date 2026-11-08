import Lamping.Lambda.BetaPaths
namespace Lamping.Lambda

theorem rename_contract (ρ : Nat → Nat) (b a : Term) :
    rename ρ (contract b a) = contract (rename (liftRen ρ) b) (rename ρ a) := by
  simp only [contract,rename_subst,subst_rename]
  congr 1
  funext i
  cases i <;> rfl

/-- Lift a real contraction through a selected term context. No variable
shift is performed here: the selected subterm already has its local scope. -/
theorem BetaAt.prefix_lift (hp : subtermAt t pre=some a) (h : BetaAt a q b) :
    ∃ t', BetaAt t (pre++q) t' ∧ subtermAt t' pre=some b ∧ replaceAt t pre b=some t' := by
  induction pre generalizing t with
  | nil =>
    simp only [subtermAt,Option.some.injEq] at hp
    subst t
    exact ⟨b,h,by cases b <;> rfl,by cases a <;> rfl⟩
  | cons s pre ih =>
    cases t with
    | var i => cases s <;> simp [subtermAt] at hp
    | app f c =>
      cases s with
      | body => simp [subtermAt] at hp
      | fn =>
        obtain ⟨f',⟨body,arg,redex,replace⟩,focus,outer⟩ := ih hp
        exact ⟨.app f' c,⟨body,arg,redex,by simp [replaceAt,replace]⟩,focus,by simp [replaceAt,outer]⟩
      | arg =>
        obtain ⟨c',⟨body,arg,redex,replace⟩,focus,outer⟩ := ih hp
        exact ⟨.app f c',⟨body,arg,redex,by simp [replaceAt,replace]⟩,focus,by simp [replaceAt,outer]⟩
    | lam c =>
      cases s with
      | fn => simp [subtermAt] at hp
      | arg => simp [subtermAt] at hp
      | body =>
        obtain ⟨c',⟨body,arg,redex,replace⟩,focus,outer⟩ := ih hp
        exact ⟨.lam c',⟨body,arg,redex,by simp [replaceAt,replace]⟩,focus,by simp [replaceAt,outer]⟩

/-- Conversely, contraction below a fixed occurrence is a contraction of that
actual subterm, and the ambient target is its structural replacement. -/
theorem BetaAt.prefix_reflect (hp : subtermAt t pre=some a) (h : BetaAt t (pre++q) t') :
    ∃ b, BetaAt a q b ∧ replaceAt t pre b=some t' ∧ subtermAt t' pre=some b := by
  obtain ⟨body,arg,redex,replace⟩ := h
  have localRedex : subtermAt a q=some (.app (.lam body) arg) := by
    simpa only [subtermAt_append,hp,Option.bind_some] using redex
  obtain ⟨b,hb,_⟩ := replaceAt_lookup localRedex (contract body arg)
  obtain ⟨u,hu,focus,outer⟩ := (show BetaAt a q b from ⟨body,arg,localRedex,hb⟩).prefix_lift hp
  have same : u=t' := by
    -- A contraction at a fixed occurrence has a unique reduct.
    have sameRedex : subtermAt t (pre++q)=some (.app (.lam body) arg) := redex
    obtain ⟨b',a',hr,hw⟩ := (show BetaAt t (pre++q) u from hu)
    rw [sameRedex] at hr
    cases hr
    rw [replace] at hw
    exact Option.some.inj hw.symm
  subst u
  exact ⟨b,⟨body,arg,localRedex,hb⟩,outer,focus⟩

theorem BetaAt.unique (h : BetaAt t p u) (k : BetaAt t p v) : u=v := by
  obtain ⟨b,a,hr,hw⟩ := h
  obtain ⟨b',a',hr',hw'⟩ := k
  rw [hr] at hr'
  cases hr'
  rw [hw] at hw'
  exact Option.some.inj hw'

/-- Renaming at the local binder depth of an occurrence. -/
def occurrenceRenaming (ρ : Nat → Nat) : Path → (Nat → Nat)
  | [] => ρ
  | .body::p => occurrenceRenaming (liftRen ρ) p
  | _::p => occurrenceRenaming ρ p

theorem subtermAt_rename (ρ : Nat → Nat) (t : Term) (p : Path) :
    subtermAt (rename ρ t) p = (subtermAt t p).map (rename (occurrenceRenaming ρ p)) := by
  induction p generalizing ρ t with
  | nil => cases t <;> rfl
  | cons s p ih => cases t <;> cases s <;> simp [rename,subtermAt,occurrenceRenaming,ih]

theorem replaceAt_rename (ρ : Nat → Nat) (t b : Term) (p : Path) :
    replaceAt (rename ρ t) p (rename (occurrenceRenaming ρ p) b) =
      (replaceAt t p b).map (rename ρ) := by
  induction p generalizing ρ t with
  | nil => cases t <;> rfl
  | cons s p ih =>
    cases t <;> cases s <;>
      simp [rename,replaceAt,occurrenceRenaming,ih,Option.map_map,Function.comp_def]

theorem BetaAt.rename (h : BetaAt t p u) (ρ : Nat → Nat) :
    BetaAt (Lambda.rename ρ t) p (Lambda.rename ρ u) := by
  obtain ⟨b,a,hr,hw⟩ := h
  refine ⟨Lambda.rename (liftRen (occurrenceRenaming ρ p)) b,
    Lambda.rename (occurrenceRenaming ρ p) a,?_,?_⟩
  · rw [subtermAt_rename,hr]
    rfl
  · rw [←rename_contract,replaceAt_rename,hw]
    rfl

/-- Renaming reflects contractions even when it identifies free variables:
it preserves the syntax constructors and the selected occurrence. -/
theorem BetaAt.rename_reflect (h : BetaAt (Lambda.rename ρ t) p u') :
    ∃ u, BetaAt t p u ∧ Lambda.rename ρ u=u' := by
  obtain ⟨b',a',hr',hw'⟩ := h
  have hr := hr'
  rw [subtermAt_rename] at hr
  cases he : subtermAt t p with
  | none => simp [he] at hr
  | some term =>
    simp only [he,Option.map_some,Option.some.injEq] at hr
    cases term with
    | var i => cases hr
    | lam b => cases hr
    | app f a =>
      cases f with
      | var i => cases hr
      | app f c => cases hr
      | lam b =>
        obtain ⟨u,hw,_⟩ := replaceAt_lookup he (contract b a)
        have original : BetaAt t p u := ⟨b,a,he,hw⟩
        exact ⟨u,original,(original.rename ρ).unique ⟨b',a',hr',hw'⟩⟩
end Lamping.Lambda


