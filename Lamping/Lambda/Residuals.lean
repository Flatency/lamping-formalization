import Lamping.Lambda.Developments
import Lamping.Lambda.BetaPaths
namespace Lamping.Lambda.Marked

/-- Passive tags may only name redex applications. -/
def Valid : Marked → Prop
  | .var _ => True
  | .lam b => Valid b
  | .app l f a => Valid f ∧ Valid a ∧ (l ≠ [] → ∃ b, f = .lam b)
  | .red _ b a => Valid b ∧ Valid a

def activePositions : Marked → List Path
  | .var _ => []
  | .lam b => (activePositions b).map (.body :: ·)
  | .app _ f a => (activePositions f).map (.fn :: ·) ++ (activePositions a).map (.arg :: ·)
  | .red _ b a => [] :: ((activePositions b).map (fun p => .fn :: .body :: p) ++
      (activePositions a).map (.arg :: ·))

/-- Read an old name, rather than enumerate redexes of the endpoint. -/
def tracePositions (r : Path) : Marked → List Path
  | .var _ => []
  | .lam b => (tracePositions r b).map (.body :: ·)
  | .app l f a => (if r ∈ l then [[]] else []) ++
      ((tracePositions r f).map (.fn :: ·) ++ (tracePositions r a).map (.arg :: ·))
  | .red l b a => (if r ∈ l then [[]] else []) ++
      ((tracePositions r b).map (fun p => .fn :: .body :: p) ++
      (tracePositions r a).map (.arg :: ·))

inductive StepAt : Path → Marked → Marked → Prop where
  | root (l b a) : StepAt [] (.red l b a) (contract b a)
  | lam : StepAt p b b' → StepAt (.body :: p) (.lam b) (.lam b')
  | appL : StepAt p f f' → StepAt (.fn :: p) (.app l f a) (.app l f' a)
  | appR : StepAt p a a' → StepAt (.arg :: p) (.app l f a) (.app l f a')
  | redL : StepAt p b b' → StepAt (.fn :: .body :: p) (.red l b a) (.red l b' a)
  | redR : StepAt p a a' → StepAt (.arg :: p) (.red l b a) (.red l b a')

theorem StepAt.step (h : StepAt p t u) : Step t u := by
  induction h with
  | root l b a => exact .root l b a
  | lam h ih => exact .lam ih
  | appL h ih => exact .appL ih
  | appR h ih => exact .appR ih
  | redL h ih => exact .redL ih
  | redR h ih => exact .redR ih

theorem Step.at (h : Step t u) : ∃ p, StepAt p t u := by
  induction h with
  | root l b a => exact ⟨[], .root l b a⟩
  | lam h ih => obtain ⟨p, hp⟩ := ih; exact ⟨.body :: p, .lam hp⟩
  | appL h ih => obtain ⟨p, hp⟩ := ih; exact ⟨.fn :: p, .appL hp⟩
  | appR h ih => obtain ⟨p, hp⟩ := ih; exact ⟨.arg :: p, .appR hp⟩
  | redL h ih => obtain ⟨p, hp⟩ := ih; exact ⟨.fn :: .body :: p, .redL hp⟩
  | redR h ih => obtain ⟨p, hp⟩ := ih; exact ⟨.arg :: p, .redR hp⟩

theorem StepAt.betaAt (h : StepAt p t u) : BetaAt t.erase p u.erase := by
  induction h with
  | root l b a => exact ⟨b.erase, a.erase, rfl, by simp [erase_contract, replaceAt]⟩
  | lam h ih =>
    obtain ⟨b, a, hl, hr⟩ := ih
    exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩
  | appL h ih =>
    obtain ⟨b, a, hl, hr⟩ := ih
    exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩
  | appR h ih =>
    obtain ⟨b, a, hl, hr⟩ := ih
    exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩
  | redL h ih =>
    obtain ⟨b, a, hl, hr⟩ := ih
    exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩
  | redR h ih =>
    obtain ⟨b, a, hl, hr⟩ := ih
    exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩

theorem StepAt.active (h : StepAt p t u) : p ∈ activePositions t := by
  induction h with
  | root l b a => simp [activePositions]
  | lam h ih => simpa [activePositions] using ih
  | appL h ih => simp [activePositions, ih]
  | appR h ih => simp [activePositions, ih]
  | redL h ih => simp [activePositions, ih]
  | redR h ih => simp [activePositions, ih]

theorem active_has_step {t : Marked} {p : Path} (h : p ∈ activePositions t) :
    ∃ u, StepAt p t u := by
  induction t generalizing p with
  | var i => simp [activePositions] at h
  | lam b hb =>
    simp only [activePositions, List.mem_map] at h
    obtain ⟨q, hq, rfl⟩ := h
    obtain ⟨u, hu⟩ := hb hq
    exact ⟨.lam u, .lam hu⟩
  | app l f a hf ha =>
    simp only [activePositions, List.mem_append, List.mem_map] at h
    rcases h with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨u, hu⟩ := hf hq; exact ⟨.app l u a, .appL hu⟩
    · obtain ⟨u, hu⟩ := ha hq; exact ⟨.app l f u, .appR hu⟩
  | red l b a hb ha =>
    simp only [activePositions, List.mem_cons, List.mem_append, List.mem_map] at h
    rcases h with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨contract b a, .root l b a⟩
    · obtain ⟨u, hu⟩ := hb hq; exact ⟨.red l u a, .redL hu⟩
    · obtain ⟨u, hu⟩ := ha hq; exact ⟨.red l b u, .redR hu⟩

theorem active_iff_stepAt (t : Marked) (p : Path) :
    p ∈ activePositions t ↔ ∃ u, StepAt p t u :=
  ⟨active_has_step, fun ⟨_, h⟩ => h.active⟩

/-- Every actual beta contraction at a selected path lifts, with the same
    target term; this covers arbitrary relative schedules. -/
theorem lift_betaAt (ha : p ∈ activePositions t) (hβ : BetaAt t.erase p v) :
    ∃ u, StepAt p t u ∧ u.erase = v := by
  obtain ⟨u, hu⟩ := active_has_step ha
  obtain ⟨b, a, hl, hr⟩ := hu.betaAt
  obtain ⟨b', a', hl', hr'⟩ := hβ
  have eq : Term.app (.lam b) a = Term.app (.lam b') a' := Option.some.inj (hl.symm.trans hl')
  cases eq
  exact ⟨u, hu, Option.some.inj (hr.symm.trans hr')⟩




theorem valid_rename (ht : Valid t) (ρ) : Valid (rename ρ t) := by
  induction t generalizing ρ with
  | var i => trivial
  | lam b hb => exact hb ht _
  | red l b a hb ha => exact ⟨hb ht.1 _, ha ht.2 _⟩
  | app l f a hf ha =>
    refine ⟨hf ht.1 _, ha ht.2.1 _, ?_⟩
    intro hl
    obtain ⟨b, rfl⟩ := ht.2.2 hl
    exact ⟨rename (liftRen ρ) b, rfl⟩

theorem valid_subst (ht : Valid t) (hσ : ∀ i, Valid (σ i)) : Valid (subst σ t) := by
  induction t generalizing σ with
  | var i => exact hσ i
  | lam b hb =>
    apply hb ht
    intro i; cases i with
    | zero => trivial
    | succ i => exact valid_rename (hσ i) _
  | red l b a hb ha =>
    refine ⟨hb ht.1 ?_, ha ht.2 hσ⟩
    intro i; cases i with
    | zero => trivial
    | succ i => exact valid_rename (hσ i) _
  | app l f a hf ha =>
    refine ⟨hf ht.1 hσ, ha ht.2.1 hσ, ?_⟩
    intro hl
    obtain ⟨b, rfl⟩ := ht.2.2 hl
    exact ⟨subst (liftSub σ) b, rfl⟩

theorem Step.valid (h : Step t u) (ht : Valid t) : Valid u := by
  induction h with
  | root l b a =>
    apply valid_subst ht.1
    intro i; cases i with
    | zero => exact ht.2
    | succ i => trivial
  | lam h ih => exact ih ht
  | appR h ih => exact ⟨ht.1, ih ht.2.1, ht.2.2⟩
  | redL h ih => exact ⟨ih ht.1, ht.2⟩
  | redR h ih => exact ⟨ht.1, ih ht.2⟩
  | appL h ih =>
    refine ⟨ih ht.1, ht.2.1, ?_⟩
    intro hl
    obtain ⟨b, he⟩ := ht.2.2 hl
    subst he
    cases h with
    | lam hs => exact ⟨_, rfl⟩

theorem Steps.valid (h : Steps t u) (ht : Valid t) : Valid u := by
  induction h with
  | refl => exact ht
  | cons h hs ih => exact ih (h.valid ht)

private theorem mem_rootTrace (r : Path) (l : List Path) (p : Path) :
    p ∈ (if r ∈ l then [[]] else []) ↔ p = [] ∧ r ∈ l := by
  by_cases hr : r ∈ l <;> simp [hr]

theorem tracePositions_sound (ht : Valid t) (h : p ∈ tracePositions r t) :
    ∃ u, subtermAt t.erase p = some u ∧ IsRedex u := by
  induction t generalizing p with
  | var i => simp [tracePositions] at h
  | lam b hb =>
    simp only [tracePositions, List.mem_map] at h
    obtain ⟨q, hq, rfl⟩ := h
    obtain ⟨u, hu, hr⟩ := hb ht hq
    exact ⟨u, hu, hr⟩
  | app l f a hf ha =>
    simp only [tracePositions, List.mem_append, List.mem_map] at h
    rcases h with hp | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨rfl, hr⟩ := (mem_rootTrace r l p).mp hp
      have hl : l ≠ [] := by intro he; simp [he] at hr
      obtain ⟨b, he⟩ := ht.2.2 hl
      exact ⟨(Marked.app l f a).erase, rfl, by simp [erase, he, IsRedex]⟩
    · obtain ⟨u, hu, hr⟩ := hf ht.1 hq
      exact ⟨u, hu, hr⟩
    · obtain ⟨u, hu, hr⟩ := ha ht.2.1 hq
      exact ⟨u, hu, hr⟩
  | red l b a hb ha =>
    simp only [tracePositions, List.mem_append, List.mem_map] at h
    rcases h with hp | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨rfl, hr⟩ := (mem_rootTrace r l p).mp hp
      exact ⟨(Marked.red l b a).erase, rfl, trivial⟩
    · obtain ⟨u, hu, hr⟩ := hb ht.1 hq
      exact ⟨u, hu, hr⟩
    · obtain ⟨u, hu, hr⟩ := ha ht.2 hq
      exact ⟨u, hu, hr⟩

/-- A finite enumeration of actual RedexOcc values for the old name r. -/
def residuals (ht : Valid t) (r : Path) : List (RedexOcc t.erase) :=
  (tracePositions r t).attach.map (fun p => ⟨p.val, tracePositions_sound ht p.property⟩)

theorem mem_residuals (ht : Valid t) (r p : Path) :
    (∃ q ∈ residuals ht r, q.val = p) ↔ p ∈ tracePositions r t := by
  simp only [residuals, List.mem_map, List.mem_attach, true_and]
  constructor
  · rintro ⟨q, ⟨u, rfl⟩, rfl⟩; exact u.property
  · intro h; exact ⟨⟨p, tracePositions_sound ht h⟩, ⟨⟨p, h⟩, rfl⟩, rfl⟩

/-- Single and composed transport retain the same names; no reinitialization. -/
def residualAfterStep (h : Step t u) (ht : Valid t) (r : Path) : List (RedexOcc u.erase) :=
  residuals (h.valid ht) r

def residualAfterSteps (h : Steps t u) (ht : Valid t) (r : Path) : List (RedexOcc u.erase) :=
  residuals (h.valid ht) r

theorem complete_term_independent (h : Complete t u) (k : Complete t v) : u.erase = v.erase :=
  congrArg erase (complete_unique h k)

theorem complete_residual_independent (h : Complete t u) (k : Complete t v) (r : Path) :
    tracePositions r u = tracePositions r v :=
  congrArg (tracePositions r) (complete_unique h k)

theorem complete_active_empty (h : Complete t u) : activePositions u = [] := by
  have hn := h.2
  clear h
  induction u with
  | var i => rfl
  | lam b hb => simp [activePositions, hb hn]
  | app l f a hf ha => simp [activePositions, hf hn.1, ha hn.2]
  | red l b a hb ha => exact False.elim hn





/-- General beta transport: passive and freshly created redexes can also fire.
    The active-only Step relation above is the development restriction. -/
inductive ReductionAt : Path → Marked → Marked → Prop where
  | appRoot (l b a) : ReductionAt [] (.app l (.lam b) a) (contract b a)
  | redRoot (l b a) : ReductionAt [] (.red l b a) (contract b a)
  | lam : ReductionAt p b b' → ReductionAt (.body :: p) (.lam b) (.lam b')
  | appL : ReductionAt p f f' → ReductionAt (.fn :: p) (.app l f a) (.app l f' a)
  | appR : ReductionAt p a a' → ReductionAt (.arg :: p) (.app l f a) (.app l f a')
  | redL : ReductionAt p b b' → ReductionAt (.fn :: .body :: p) (.red l b a) (.red l b' a)
  | redR : ReductionAt p a a' → ReductionAt (.arg :: p) (.red l b a) (.red l b a')

theorem ReductionAt.betaAt (h : ReductionAt p t u) : BetaAt t.erase p u.erase := by
  induction h with
  | appRoot l b a => exact ⟨b.erase, a.erase, rfl, by simp [erase_contract, replaceAt]⟩
  | redRoot l b a => exact ⟨b.erase, a.erase, rfl, by simp [erase_contract, replaceAt]⟩
  | lam h ih => obtain ⟨b, a, hl, hr⟩ := ih; exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩
  | appL h ih => obtain ⟨b, a, hl, hr⟩ := ih; exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩
  | appR h ih => obtain ⟨b, a, hl, hr⟩ := ih; exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩
  | redL h ih => obtain ⟨b, a, hl, hr⟩ := ih; exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩
  | redR h ih => obtain ⟨b, a, hl, hr⟩ := ih; exact ⟨b, a, hl, by simp [erase, replaceAt, hr]⟩

theorem StepAt.reductionAt (h : StepAt p t u) : ReductionAt p t u := by
  induction h with
  | root l b a => exact .redRoot l b a
  | lam h ih => exact .lam ih
  | appL h ih => exact .appL ih
  | appR h ih => exact .appR ih
  | redL h ih => exact .redL ih
  | redR h ih => exact .redR ih

private theorem erase_lam {f : Marked} (h : f.erase = .lam b) :
    ∃ c, f = .lam c ∧ c.erase = b := by
  cases f with
  | var i => simp [erase] at h
  | app l f a => simp [erase] at h
  | red l b a => simp [erase] at h
  | lam c => exact ⟨c, rfl, Term.lam.inj h⟩

/-- Lifting for arbitrary true beta paths, including unselected/new redexes. -/
theorem lift_general_betaAt {t : Marked} {p : Path} {v : Term} (h : BetaAt t.erase p v) :
    ∃ u, ReductionAt p t u ∧ u.erase = v := by
  obtain ⟨b, a, hl, hr⟩ := h
  induction p generalizing t v with
  | nil =>
    simp only [subtermAt, Option.some.injEq] at hl
    simp only [replaceAt, Option.some.injEq] at hr
    cases t with
    | var i => simp [erase] at hl
    | lam c => simp [erase] at hl
    | app l f x =>
      simp only [erase, Term.app.injEq] at hl
      obtain ⟨c, rfl, hc⟩ := erase_lam hl.1
      exact ⟨contract c x, .appRoot l c x, by simp [erase_contract, hc, hl.2, hr]⟩
    | red l c x =>
      simp only [erase, Term.app.injEq, Term.lam.injEq] at hl
      exact ⟨contract c x, .redRoot l c x, by simp [erase_contract, hl.1, hl.2, hr]⟩
  | cons s p ih =>
    cases t with
    | var i => cases s <;> simp [erase, subtermAt] at hl
    | lam c =>
      cases s with
      | fn => simp [erase, subtermAt] at hl
      | arg => simp [erase, subtermAt] at hl
      | body =>
        simp only [erase, subtermAt] at hl
        simp only [erase, replaceAt] at hr
        cases he : replaceAt c.erase p (Lambda.contract b a) with
        | none => simp [he] at hr
        | some w =>
          simp only [he, Option.map_some, Option.some.injEq] at hr
          obtain ⟨u, hu, heq⟩ := ih hl he
          exact ⟨.lam u, .lam hu, by simp [erase, heq, hr]⟩
    | app l f x =>
      cases s with
      | body => simp [erase, subtermAt] at hl
      | fn =>
        simp only [erase, subtermAt] at hl
        simp only [erase, replaceAt] at hr
        cases he : replaceAt f.erase p (Lambda.contract b a) with
        | none => simp [he] at hr
        | some w =>
          simp only [he, Option.map_some, Option.some.injEq] at hr
          obtain ⟨u, hu, heq⟩ := ih hl he
          exact ⟨.app l u x, .appL hu, by simp [erase, heq, hr]⟩
      | arg =>
        simp only [erase, subtermAt] at hl
        simp only [erase, replaceAt] at hr
        cases he : replaceAt x.erase p (Lambda.contract b a) with
        | none => simp [he] at hr
        | some w =>
          simp only [he, Option.map_some, Option.some.injEq] at hr
          obtain ⟨u, hu, heq⟩ := ih hl he
          exact ⟨.app l f u, .appR hu, by simp [erase, heq, hr]⟩
    | red l c x =>
      cases s with
      | body => simp [erase, subtermAt] at hl
      | arg =>
        simp only [erase, subtermAt] at hl
        simp only [erase, replaceAt] at hr
        cases he : replaceAt x.erase p (Lambda.contract b a) with
        | none => simp [he] at hr
        | some w =>
          simp only [he, Option.map_some, Option.some.injEq] at hr
          obtain ⟨u, hu, heq⟩ := ih hl he
          exact ⟨.red l c u, .redR hu, by simp [erase, heq, hr]⟩
      | fn =>
        cases p with
        | nil => simp [erase, subtermAt] at hl
        | cons s q =>
          cases s with
          | fn => simp [erase, subtermAt] at hl
          | arg => simp [erase, subtermAt] at hl
          | body =>
            simp only [erase, subtermAt] at hl
            simp only [erase, replaceAt] at hr
            cases he : replaceAt c.erase q (Lambda.contract b a) with
            | none => simp [he] at hr
            | some w =>
              simp only [he, Option.map_some, Option.some.injEq] at hr
              obtain ⟨z, hz, heq⟩ := ih (t := .lam c) (v := .lam w) hl
                (by simp [erase, replaceAt, he])
              cases hz with
              | lam hz =>
                rename_i u
                have hu : u.erase = w := Term.lam.inj heq
                exact ⟨.red l u x, .redL hz, by simp [erase, hu, hr]⟩




theorem ReductionAt.valid (h : ReductionAt p t u) (ht : Valid t) : Valid u := by
  induction h with
  | appRoot l b a =>
    apply valid_subst (t := b) ht.1
    intro i; cases i with
    | zero => exact ht.2.1
    | succ i => trivial
  | redRoot l b a =>
    apply valid_subst ht.1
    intro i; cases i with
    | zero => exact ht.2
    | succ i => trivial
  | lam h ih => exact ih ht
  | appR h ih => exact ⟨ht.1, ih ht.2.1, ht.2.2⟩
  | redL h ih => exact ⟨ih ht.1, ht.2⟩
  | redR h ih => exact ⟨ht.1, ih ht.2⟩
  | appL h ih =>
    refine ⟨ih ht.1, ht.2.1, ?_⟩
    intro hl
    obtain ⟨b, he⟩ := ht.2.2 hl
    subst he
    cases h with
    | lam hs => exact ⟨_, rfl⟩

theorem ReductionAt.deterministic (h : ReductionAt p t u) (k : ReductionAt p t v) : u = v := by
  induction h generalizing v with
  | appRoot l b a => cases k; rfl
  | redRoot l b a => cases k; rfl
  | lam h ih => cases k with | lam k => exact congrArg Marked.lam (ih k)
  | appL h ih => cases k with | appL k => exact congrArg (fun f => Marked.app _ f _) (ih k)
  | appR h ih => cases k with | appR k => exact congrArg (fun a => Marked.app _ _ a) (ih k)
  | redL h ih => cases k with | redL k => exact congrArg (fun b => Marked.red _ b _) (ih k)
  | redR h ih => cases k with | redR k => exact congrArg (fun a => Marked.red _ _ a) (ih k)

/-- Position-indexed arbitrary beta histories transport the same original names. -/
inductive History : List Path → Marked → Marked → Prop where
  | nil (t) : History [] t t
  | cons : ReductionAt p t u → History ps u v → History (p :: ps) t v

theorem History.append (h : History ps t u) (k : History qs u v) : History (ps ++ qs) t v := by
  induction h with
  | nil => exact k
  | cons h hs ih => exact .cons h (ih k)

theorem History.valid (h : History ps t u) (ht : Valid t) : Valid u := by
  induction h with
  | nil => exact ht
  | cons h hs ih => exact ih (h.valid ht)

theorem History.erase (h : History ps t u) : Betas t.erase u.erase := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => exact .cons h.betaAt.beta ih

theorem History.deterministic (h : History ps t u) (k : History ps t v) : u = v := by
  induction h generalizing v with
  | nil => cases k; rfl
  | cons h hs ih =>
    cases k with
    | cons k ks =>
      cases h.deterministic k
      exact ih ks

theorem lift_betas {m n : Term} (h : Betas m n) (t : Marked) (ht : t.erase = m) :
    ∃ ps u, History ps t u ∧ u.erase = n := by
  induction h generalizing t with
  | refl m => exact ⟨[], t, .nil t, ht⟩
  | @cons m n k hb hs ih =>
    obtain ⟨p, hp⟩ := beta_iff_betaAt.mp hb
    rw [← ht] at hp
    obtain ⟨u, hu, he⟩ := lift_general_betaAt hp
    obtain ⟨ps, v, hv, hev⟩ := ih u he
    exact ⟨p :: ps, v, .cons hu hv, hev⟩

def residualAfterReduction (h : ReductionAt p t u) (ht : Valid t) (r : Path) :
    List (RedexOcc u.erase) := residuals (h.valid ht) r

def residualAfterHistory (h : History ps t u) (ht : Valid t) (r : Path) :
    List (RedexOcc u.erase) := residuals (h.valid ht) r

/-- Composite transport is ordinary history concatenation, without re-tagging. -/
theorem residual_composition (h : History ps t u) (k : History qs u v) (ht : Valid t) (r : Path) :
    residualAfterHistory (h.append k) ht r = residualAfterHistory k (h.valid ht) r := rfl

theorem Steps.history (h : Steps t u) : ∃ ps, History ps t u := by
  induction h with
  | refl => exact ⟨[], .nil _⟩
  | cons h hs ih =>
    obtain ⟨p, hp⟩ := h.at
    obtain ⟨ps, hps⟩ := ih
    exact ⟨p :: ps, .cons hp.reductionAt hps⟩

end Lamping.Lambda.Marked

