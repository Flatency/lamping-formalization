import Lamping.Lambda.Labels
import Lamping.Lambda.Histories
namespace Lamping.Lambda.Labelled

/-- Actual contraction path, transporting the existing labels without INIT. -/
inductive StepAt : Path → LTerm → LTerm → Prop where
  | root (beta alpha b a) : StepAt [] (.app beta (.lam alpha b) a)
      (LTerm.contract beta alpha b a)
  | fn : StepAt p f f' → StepAt (.fn :: p) (.app beta f a) (.app beta f' a)
  | arg : StepAt p a a' → StepAt (.arg :: p) (.app beta f a) (.app beta f a')
  | body : StepAt p b b' → StepAt (.body :: p) (.lam alpha b) (.lam alpha b')

theorem StepAt.betaAt (h : StepAt p t u) : BetaAt t.erase p u.erase := by
  induction h with
  | root beta alpha b a => exact ⟨b.erase,a.erase,rfl,by simp [LTerm.erase_contract,replaceAt]⟩
  | fn h ih => obtain ⟨b,a,hl,hr⟩ := ih; exact ⟨b,a,hl,by simp [LTerm.erase,replaceAt,hr]⟩
  | arg h ih => obtain ⟨b,a,hl,hr⟩ := ih; exact ⟨b,a,hl,by simp [LTerm.erase,replaceAt,hr]⟩
  | body h ih => obtain ⟨b,a,hl,hr⟩ := ih; exact ⟨b,a,hl,by simp [LTerm.erase,replaceAt,hr]⟩

theorem StepAt.labelledBeta (h : StepAt p t u) : LBETA t u := by
  induction h with
  | root beta alpha b a => exact .root beta alpha b a
  | fn _ ih => exact .fn ih
  | arg _ ih => exact .arg ih
  | body _ ih => exact .body ih

theorem StepAt.deterministic (h : StepAt p t u) (k : StepAt p t v) : u=v := by
  induction h generalizing v with
  | root beta alpha b a => cases k; rfl
  | fn h ih => cases k with | fn k => exact congrArg (fun f => LTerm.app _ f _) (ih k)
  | arg h ih => cases k with | arg k => exact congrArg (fun a => LTerm.app _ _ a) (ih k)
  | body h ih => cases k with | body k => exact congrArg (LTerm.lam _) (ih k)

private theorem erase_lam {f : LTerm} (h : f.erase = .lam b) :
    ∃ alpha c, f = .lam alpha c ∧ c.erase = b := by
  cases f with
  | var _ _ => simp [LTerm.erase] at h
  | app _ _ _ => simp [LTerm.erase] at h
  | lam alpha c => exact ⟨alpha,c,rfl,Term.lam.inj h⟩

/-- Every real unlabelled contraction lifts from every existing labelling. -/
theorem lift_betaAt {t : LTerm} (h : BetaAt t.erase p v) :
    ∃ u, StepAt p t u ∧ u.erase=v := by
  obtain ⟨b,a,hl,hr⟩ := h
  induction p generalizing t v with
  | nil =>
    simp only [subtermAt,Option.some.injEq] at hl
    simp only [replaceAt,Option.some.injEq] at hr
    cases t with
    | var _ _ => simp [LTerm.erase] at hl
    | lam _ _ => simp [LTerm.erase] at hl
    | app beta f x =>
      simp only [LTerm.erase,Term.app.injEq] at hl
      obtain ⟨alpha,c,rfl,hc⟩ := erase_lam hl.1
      exact ⟨_,.root beta alpha c x,by simp [LTerm.erase_contract,hc,hl.2,hr]⟩
  | cons s p ih =>
    cases t with
    | var _ _ => cases s <;> simp [LTerm.erase,subtermAt] at hl
    | lam alpha c =>
      cases s with
      | fn => simp [LTerm.erase,subtermAt] at hl
      | arg => simp [LTerm.erase,subtermAt] at hl
      | body =>
        simp only [LTerm.erase,subtermAt] at hl
        simp only [LTerm.erase,replaceAt] at hr
        cases he : replaceAt c.erase p (Lambda.contract b a) with
        | none => simp [he] at hr
        | some w =>
          simp only [he,Option.map_some,Option.some.injEq] at hr
          obtain ⟨u,hu,heq⟩ := ih hl he
          exact ⟨.lam alpha u,.body hu,by simp [LTerm.erase,heq,hr]⟩
    | app beta f x =>
      cases s with
      | body => simp [LTerm.erase,subtermAt] at hl
      | fn =>
        simp only [LTerm.erase,subtermAt] at hl
        simp only [LTerm.erase,replaceAt] at hr
        cases he : replaceAt f.erase p (Lambda.contract b a) with
        | none => simp [he] at hr
        | some w =>
          simp only [he,Option.map_some,Option.some.injEq] at hr
          obtain ⟨u,hu,heq⟩ := ih hl he
          exact ⟨.app beta u x,.fn hu,by simp [LTerm.erase,heq,hr]⟩
      | arg =>
        simp only [LTerm.erase,subtermAt] at hl
        simp only [LTerm.erase,replaceAt] at hr
        cases he : replaceAt x.erase p (Lambda.contract b a) with
        | none => simp [he] at hr
        | some w =>
          simp only [he,Option.map_some,Option.some.injEq] at hr
          obtain ⟨u,hu,heq⟩ := ih hl he
          exact ⟨.app beta f u,.arg hu,by simp [LTerm.erase,heq,hr]⟩

inductive History : List Path → LTerm → LTerm → Prop where
  | nil (t) : History [] t t
  | cons : StepAt p t u → History ps u v → History (p::ps) t v

theorem History.betaHistory (h : History ps t u) : BetaHistory ps t.erase u.erase := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons h.betaAt ih

theorem History.deterministic (h : History ps t u) (k : History ps t v) : u=v := by
  induction h generalizing v with
  | nil => cases k; rfl
  | cons h _ ih =>
    cases k with
    | cons k ks => cases h.deterministic k; exact ih ks

theorem History.append (h : History ps t u) (k : History qs u v) : History (ps++qs) t v := by
  induction h with
  | nil => exact k
  | cons h _ ih => exact .cons h (ih k)

theorem lift_history (h : BetaHistory ps m n) (t : LTerm) (ht : t.erase=m) :
    ∃ u, History ps t u ∧ u.erase=n := by
  induction h generalizing t with
  | nil => exact ⟨t,.nil t,ht⟩
  | cons hb _ ih =>
    rw [← ht] at hb
    obtain ⟨u,hu,he⟩ := lift_betaAt hb
    obtain ⟨v,hv,hve⟩ := ih u he
    exact ⟨v,.cons hu hv,hve⟩

/-- Unique transport from an arbitrary fixed initial labelling, not re-INIT. -/
theorem Derivation.label_transport (h : Derivation m n) (t : LTerm) (ht : t.erase=m) :
    ∃ u, History h.paths t u ∧ u.erase=n ∧ ∀ v, History h.paths t v → v=u := by
  obtain ⟨u,hu,he⟩ := lift_history h.valid t ht
  exact ⟨u,hu,he,fun _ hv => hv.deterministic hu⟩

end Lamping.Lambda.Labelled


namespace Lamping.Lambda.Labelled
namespace LTerm
/-- Label-aware lookup at the same syntax occurrence as the unlabelled term. -/
def subterm : LTerm → Path → Option LTerm
  | t, [] => some t
  | .app _ f _, .fn::p => subterm f p
  | .app _ _ a, .arg::p => subterm a p
  | .lam _ b, .body::p => subterm b p
  | _, _ => none

def degreeAt (t : LTerm) (p : Path) : Option Label := (t.subterm p).bind degree

/-- One deterministic, executable contraction; invalid paths return none. -/
def reduceAt : LTerm → Path → Option LTerm
  | .app beta (.lam alpha b) a, [] => some (contract beta alpha b a)
  | .app beta f a, .fn::p => (reduceAt f p).map (fun f' => .app beta f' a)
  | .app beta f a, .arg::p => (reduceAt a p).map (.app beta f)
  | .lam alpha b, .body::p => (reduceAt b p).map (.lam alpha)
  | _, _ => none

def replay : LTerm → List Path → Option LTerm
  | t, [] => some t
  | t, p::ps => (reduceAt t p).bind (fun u => replay u ps)

theorem erase_subterm (t : LTerm) (p : Path) :
    (subterm t p).map erase = subtermAt t.erase p := by
  induction p generalizing t with
  | nil => simp [subterm,subtermAt]
  | cons s p ih => cases t <;> cases s <;> simp [subterm,subtermAt,erase,ih]
end LTerm

theorem StepAt.reduceAt (h : StepAt p t u) : t.reduceAt p = some u := by
  induction h with
  | root => rfl
  | fn _ ih => simp [LTerm.reduceAt,ih]
  | arg _ ih => simp [LTerm.reduceAt,ih]
  | body _ ih => simp [LTerm.reduceAt,ih]

theorem reduceAt_step {t u : LTerm} {p : Path} (h : t.reduceAt p = some u) : StepAt p t u := by
  induction p generalizing t u with
  | nil =>
    cases t with
    | var _ _ => simp [LTerm.reduceAt] at h
    | lam _ _ => simp [LTerm.reduceAt] at h
    | app beta f a =>
      cases f with
      | var _ _ => simp [LTerm.reduceAt] at h
      | app _ _ _ => simp [LTerm.reduceAt] at h
      | lam alpha b => simp only [LTerm.reduceAt,Option.some.injEq] at h; cases h; exact .root _ _ _ _
  | cons s p ih =>
    cases t with
    | var _ _ => cases s <;> simp [LTerm.reduceAt] at h
    | app beta f a =>
      cases s with
      | body => simp [LTerm.reduceAt] at h
      | fn =>
        simp only [LTerm.reduceAt,Option.map_eq_some_iff] at h
        obtain ⟨v,hv,rfl⟩ := h
        exact .fn (ih hv)
      | arg =>
        simp only [LTerm.reduceAt,Option.map_eq_some_iff] at h
        obtain ⟨v,hv,rfl⟩ := h
        exact .arg (ih hv)
    | lam alpha b =>
      cases s with
      | fn => simp [LTerm.reduceAt] at h
      | arg => simp [LTerm.reduceAt] at h
      | body =>
        simp only [LTerm.reduceAt,Option.map_eq_some_iff] at h
        obtain ⟨v,hv,rfl⟩ := h
        exact .body (ih hv)

theorem History.replay (h : History ps t u) : t.replay ps=some u := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [LTerm.replay,h.reduceAt,ih]

theorem replay_history {t u : LTerm} {ps : List Path} (h : t.replay ps=some u) : History ps t u := by
  induction ps generalizing t with
  | nil => simp only [LTerm.replay,Option.some.injEq] at h; cases h; exact .nil _
  | cons p ps ih =>
    simp only [LTerm.replay,Option.bind_eq_some_iff] at h
    obtain ⟨v,hv,hs⟩ := h
    exact .cons (reduceAt_step hv) (ih hs)

/-- Replay covers every chosen actual schedule, preserving its target erasure. -/
theorem replay_exists (h : BetaHistory ps m n) (t : LTerm) (ht : t.erase=m) :
    ∃ u, t.replay ps=some u ∧ u.erase=n := by
  obtain ⟨u,hu,he⟩ := lift_history h t ht
  exact ⟨u,hu.replay,he⟩

/-- The degree is well-defined at every actual redex occurrence. -/
theorem degreeAt_exists (t : LTerm) (r : RedexOcc t.erase) : ∃ alpha, t.degreeAt r.val=some alpha := by
  obtain ⟨v,hv,hr⟩ := r.property
  have h := t.erase_subterm r.val
  rw [hv] at h
  cases he : t.subterm r.val with
  | none => simp [he] at h
  | some s =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    cases s with
    | var l i => cases h; cases hr
    | lam l b => cases h; cases hr
    | app l f a =>
      cases f with
      | var l' i => cases h; cases hr
      | app l' x y => cases h; cases hr
      | lam alpha b => exact ⟨alpha,by simp [LTerm.degreeAt,he,LTerm.degree]⟩
end Lamping.Lambda.Labelled

