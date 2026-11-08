import Lamping.Lambda.Histories
namespace Lamping.Lambda.Marked

/-- Substitution may copy an occurrence but never merges two old names on a
single application node. This invariant does not assert an ancestor exists. -/
def SingleTags : Marked → Prop
  | .var _ => True
  | .lam b => SingleTags b
  | .app l f a => l.length≤1 ∧ SingleTags f ∧ SingleTags a
  | .red l b a => l.length≤1 ∧ SingleTags b ∧ SingleTags a

theorem SingleTags.rename (h : SingleTags t) (ρ : Nat → Nat) : SingleTags (rename ρ t) := by
  induction t generalizing ρ with
  | var => trivial
  | lam b ih => exact ih h _
  | app l f a hf ha => exact ⟨h.1,hf h.2.1 _,ha h.2.2 _⟩
  | red l b a hb ha => exact ⟨h.1,hb h.2.1 _,ha h.2.2 _⟩

theorem SingleTags.subst (h : SingleTags t) (hσ : ∀ i, SingleTags (σ i)) :
    SingleTags (subst σ t) := by
  induction t generalizing σ with
  | var i => exact hσ i
  | lam b ih =>
    apply ih h
    intro i
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).rename Nat.succ
  | app l f a hf ha => exact ⟨h.1,hf h.2.1 hσ,ha h.2.2 hσ⟩
  | red l b a hb ha =>
    refine ⟨h.1,hb h.2.1 ?_,ha h.2.2 hσ⟩
    intro i
    cases i with
    | zero => trivial
    | succ i => exact (hσ i).rename Nat.succ

theorem SingleTags.contract (hb : SingleTags b) (ha : SingleTags a) : SingleTags (contract b a) := by
  apply hb.subst
  intro i
  cases i with
  | zero => exact ha
  | succ i => trivial

theorem ReductionAt.singleTags (h : ReductionAt p t u) (ht : SingleTags t) : SingleTags u := by
  induction h with
  | appRoot l b a => exact SingleTags.contract (b:=b) ht.2.1 ht.2.2
  | redRoot l b a => exact SingleTags.contract (b:=b) ht.2.1 ht.2.2
  | lam h ih => exact ih ht
  | appL h ih => exact ⟨ht.1,ih ht.2.1,ht.2.2⟩
  | appR h ih => exact ⟨ht.1,ht.2.1,ih ht.2.2⟩
  | redL h ih => exact ⟨ht.1,ih ht.2.1,ht.2.2⟩
  | redR h ih => exact ⟨ht.1,ht.2.1,ih ht.2.2⟩

theorem History.singleTags (h : History ps t u) (ht : SingleTags t) : SingleTags u := by
  induction h with
  | nil => exact ht
  | cons h hs ih => exact ih (h.singleTags ht)

theorem singleTags_markAt (F : List Path) (t : Term) (p : Path) : SingleTags (markAt F t p) := by
  induction t generalizing p with
  | var => trivial
  | lam b ih => exact ih _
  | app f a hf ha =>
    cases f with
    | var i => exact ⟨by decide,trivial,ha _⟩
    | app f c => exact ⟨by decide,hf _,ha _⟩
    | lam b =>
      have hb : SingleTags (markAt F b ((p++[.fn])++[.body])) := by
        simpa only [markAt,SingleTags] using hf (p++[.fn])
      simp only [markAt]
      split <;> exact ⟨by simp,hb,ha _⟩

/-- Old names attached to one actual syntax occurrence, including unselected
applications; the implicit lambda in a red node has no application names. -/
def tagsAt : Marked → Path → List Path
  | .app l _ _, [] | .red l _ _, [] => l
  | .lam b, .body::p => tagsAt b p
  | .app _ f _, .fn::p => tagsAt f p
  | .app _ _ a, .arg::p => tagsAt a p
  | .red _ b _, .fn::.body::p => tagsAt b p
  | .red _ _ a, .arg::p => tagsAt a p
  | _, _ => []

theorem mem_tagsAt (t : Marked) (r q : Path) : r ∈ tagsAt t q ↔ q ∈ tracePositions r t := by
  induction t generalizing q with
  | var i => cases q <;> simp [tagsAt,tracePositions]
  | lam b ih =>
    cases q with
    | nil => simp [tagsAt,tracePositions]
    | cons s q => cases s <;> simp [tagsAt,tracePositions,ih]
  | app l f a hf ha =>
    cases q with
    | nil => simp [tagsAt,tracePositions]
    | cons s q => cases s <;> simp [tagsAt,tracePositions,hf,ha]
  | red l b a hb ha =>
    cases q with
    | nil => simp [tagsAt,tracePositions]
    | cons s q =>
      cases s with
      | arg => simp [tagsAt,tracePositions,ha]
      | body => simp [tagsAt,tracePositions]
      | fn =>
        cases q with
        | nil => simp [tagsAt,tracePositions]
        | cons s q => cases s <;> simp [tagsAt,tracePositions,hb]

theorem SingleTags.tagsAt_length (h : SingleTags t) (q : Path) : (tagsAt t q).length≤1 := by
  induction t generalizing q with
  | var i => cases q <;> simp [tagsAt]
  | lam b ih =>
    cases q with
    | nil => simp [tagsAt]
    | cons s q => cases s <;> simp [tagsAt,ih h]
  | app l f a hf ha =>
    cases q with
    | nil => exact h.1
    | cons s q => cases s <;> simp [tagsAt,hf h.2.1,ha h.2.2]
  | red l b a hb ha =>
    cases q with
    | nil => exact h.1
    | cons s q =>
      cases s with
      | arg => exact ha h.2.2 q
      | body => simp [tagsAt]
      | fn =>
        cases q with
        | nil => simp [tagsAt]
        | cons s q => cases s <;> simp [tagsAt,hb h.2.1]

theorem SingleTags.trace_unique (h : SingleTags t)
    (hr : q ∈ tracePositions r t) (hs : q ∈ tracePositions s t) : r=s := by
  have len := h.tagsAt_length q
  have hr := (mem_tagsAt t r q).mpr hr
  have hs := (mem_tagsAt t s q).mpr hs
  cases ht : tagsAt t q with
  | nil => simp [ht] at hr
  | cons a xs =>
    cases xs with
    | nil => simp only [ht,List.mem_singleton] at hr hs; exact hr.trans hs.symm
    | cons b xs => simp [ht] at len
end Lamping.Lambda.Marked

namespace Lamping.Lambda
/-- An endpoint redex has at most one initial redex ancestor. Existence is a
separate obligation, especially for newly created redexes. -/
theorem Derivation.residual_unique_source (h : Derivation t u) (r s : RedexOcc t)
    (q : RedexOcc u) (hr : h.Residual r q) (hs : h.Residual s q) : r=s := by
  obtain ⟨v,hv,_,hr⟩ := hr
  obtain ⟨w,hw,_,hs⟩ := hs
  have eq := hw.deterministic hv
  subst w
  apply Subtype.eq
  exact (hv.singleTags (Marked.singleTags_markAt [] t [])).trace_unique hr hs
end Lamping.Lambda
