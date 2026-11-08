import Lamping.Lamping.SourceRouteEvaluation
namespace Lamping.Lambda.Labelled
open LTerm
variable {site q : Path} {source target body argument old : LTerm} {beta alpha : Label}

/-- A real contextual contraction preserves the literal evaluated stem above
its site, with the original selector and fixed principal words. -/
theorem StepAt.sourceStem_eq {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (step : StepAt site source target) :
    source.sourceStem atoms overWord underWord site=target.sourceStem atoms overWord underWord site := by
  induction step with
  | root =>
    have empty : ∀ t : LTerm,t.sourceStem atoms overWord underWord []=some [] := by
      intro t; cases t <;> rfl
    rw [empty,empty]
  | fn step ih | arg step ih | body step ih => simp only [sourceStem,ih]

theorem StepAt.contractum_at_site (step : StepAt site source target)
    (lookup : source.subterm site=some (.app beta (.lam alpha body) argument)) :
    target.subterm site=some (LTerm.contract beta alpha body argument) := by
  induction step with
  | root =>
    simp only [subterm,Option.some.injEq] at lookup
    cases lookup
    cases LTerm.contract beta alpha body argument <;> rfl
  | fn step ih | arg step ih | body step ih => exact ih lookup

/-- Capture-correct copy evaluation under an arbitrary actual context.
The contextual prefix comes from the original source, not a caller-supplied
prefix certificate or a fresh label initialization. -/
theorem StepAt.sourceTrail_copy {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (step : StepAt site source target)
    (lookup : source.subterm site=some (.app beta (.lam alpha body) argument))
    (occurs : ArgumentOccurrence body.erase q) (r : Path) :
    target.sourceTrail atoms overWord underWord (site++(q++r))=
      (source.sourceStem atoms overWord underWord site).bind (fun stem =>
        (body.sourceTrail atoms overWord underWord q).bind (fun bodyWord =>
          (argument.sourceTrail atoms overWord underWord r).map (fun argWord =>
            stem++beta.sourceWord atoms overWord underWord++overWord++bodyWord++underWord++argWord))) := by
  rw [sourceTrail_split atoms overWord underWord (step.contractum_at_site lookup),
    ←step.sourceStem_eq atoms overWord underWord,
    sourceTrail_contract_copy atoms overWord underWord beta alpha occurs r]
  cases source.sourceStem atoms overWord underWord site <;>
    cases body.sourceTrail atoms overWord underWord q <;>
    cases argument.sourceTrail atoms overWord underWord r <;> simp [List.append_assoc]

/-- The retained nonvariable formula at the same arbitrary actual site. -/
theorem StepAt.sourceTrail_nonvariable {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (step : StepAt site source target)
    (lookup : source.subterm site=some (.app beta (.lam alpha body) argument))
    (oldLookup : body.subterm q=some old) (nonvariable : ∀ stamp k,old≠.var stamp k) :
    target.sourceTrail atoms overWord underWord (site++q)=
      (source.sourceStem atoms overWord underWord site).bind (fun stem =>
        (body.sourceTrail atoms overWord underWord q).map (fun bodyWord =>
          stem++beta.sourceWord atoms overWord underWord++overWord++bodyWord)) := by
  rw [sourceTrail_split atoms overWord underWord (step.contractum_at_site lookup),
    ←step.sourceStem_eq atoms overWord underWord,
    sourceTrail_contract_nonvariable atoms overWord underWord beta alpha oldLookup nonvariable argument]
  cases source.sourceStem atoms overWord underWord site <;>
    cases body.sourceTrail atoms overWord underWord q <;> simp [List.append_assoc]

/-- The active-degree word identifies the new whole copy trail with the
PREVIOUS whole bound-variable trail, followed by the fixed reverse route
and the actual argument trail. No common-prefix equality is a caller input. -/
theorem StepAt.sourceTrail_copy_splice {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (step : StepAt site source target)
    (lookup : source.subterm site=some (.app beta (.lam alpha body) argument))
    (active : alpha.sourceWord atoms overWord underWord=overWord)
    (occurs : ArgumentOccurrence body.erase q) (r : Path) :
    target.sourceTrail atoms overWord underWord (site++(q++r))=
      (source.sourceTrail atoms overWord underWord (site++(.fn::.body::q))).bind (fun before =>
        (argument.sourceTrail atoms overWord underWord r).map (fun after => before++underWord++after)) := by
  rw [step.sourceTrail_copy atoms overWord underWord lookup occurs r,
    sourceTrail_split atoms overWord underWord lookup]
  simp only [sourceTrail,active]
  cases source.sourceStem atoms overWord underWord site <;>
    cases body.sourceTrail atoms overWord underWord q <;>
    cases argument.sourceTrail atoms overWord underWord r <;> simp [List.append_assoc]

/-- A retained body node has the SAME previous whole physical word when
the actual active-degree word is the fixed principal. This includes the
ambient word of a retained lambda; its bound body is treated separately. -/
theorem StepAt.sourceTrail_retained_nonvariable {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (step : StepAt site source target)
    (lookup : source.subterm site=some (.app beta (.lam alpha body) argument))
    (active : alpha.sourceWord atoms overWord underWord=overWord)
    (oldLookup : body.subterm q=some old) (nonvariable : ∀ stamp k,old≠.var stamp k) :
    target.sourceTrail atoms overWord underWord (site++q)=
      source.sourceTrail atoms overWord underWord (site++(.fn::.body::q)) := by
  rw [step.sourceTrail_nonvariable atoms overWord underWord lookup oldLookup nonvariable,
    sourceTrail_split atoms overWord underWord lookup]
  simp only [sourceTrail,active]
  cases source.sourceStem atoms overWord underWord site <;>
    cases body.sourceTrail atoms overWord underWord q <;> simp [List.append_assoc]

theorem StepAt.sourceTrail_retained_variable {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (step : StepAt site source target)
    (lookup : source.subterm site=some (.app beta (.lam alpha body) argument))
    (active : alpha.sourceWord atoms overWord underWord=overWord)
    (oldLookup : subtermAt body.erase q=some (.var k)) (outside : k≠binderDepth q) :
    target.sourceTrail atoms overWord underWord (site++q)=
      source.sourceTrail atoms overWord underWord (site++(.fn::.body::q)) := by
  rw [sourceTrail_split atoms overWord underWord (step.contractum_at_site lookup),
    ←step.sourceStem_eq atoms overWord underWord,
    sourceTrail_contract_retained_variable atoms overWord underWord beta alpha oldLookup outside argument,
    sourceTrail_split atoms overWord underWord lookup]
  simp only [sourceTrail,active]
  cases source.sourceStem atoms overWord underWord site <;>
    cases body.sourceTrail atoms overWord underWord q <;> simp [List.append_assoc]

/-- Paths outside the contracted subtree keep their evaluated word. Strict
ancestors are included: their own incoming edge is unchanged. Invalid paths
remain governed by Option; no lookup existence is asserted. -/
theorem StepAt.sourceTrail_outside {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    (step : StepAt site source target) (p : Path) (outside : ¬∃ suffix,p=site++suffix) :
    target.sourceTrail atoms overWord underWord p=source.sourceTrail atoms overWord underWord p := by
  induction step generalizing p with
  | root => exact False.elim (outside ⟨p,rfl⟩)
  | fn step ih =>
    cases p with
    | nil => rfl
    | cons child rest =>
      cases child with
      | body | arg => rfl
      | fn =>
        simp only [sourceTrail]
        rw [ih rest (by rintro ⟨suffix,equal⟩; exact outside ⟨suffix,congrArg (Step.fn::·) equal⟩)]
  | arg step ih =>
    cases p with
    | nil => rfl
    | cons child rest =>
      cases child with
      | body | fn => rfl
      | arg =>
        simp only [sourceTrail]
        rw [ih rest (by rintro ⟨suffix,equal⟩; exact outside ⟨suffix,congrArg (Step.arg::·) equal⟩)]
  | body step ih =>
    cases p with
    | nil => rfl
    | cons child rest =>
      cases child with
      | fn | arg => rfl
      | body =>
        simp only [sourceTrail]
        rw [ih rest (by rintro ⟨suffix,equal⟩; exact outside ⟨suffix,congrArg (Step.body::·) equal⟩)]

/-- A descendant is evaluated after the parent's WHOLE incoming path,
rather than only its stem. The child and selector are fixed by actual syntax. -/
theorem LTerm.sourceTrail_child_descendant {X : Type} (atoms : Nat → List X) (overWord underWord : List X)
    {t parent child : LTerm} {p : Path} {childStep : Step}
    (lookup : t.subterm p=some parent) (atChild : parent.subterm [childStep]=some child) (q : Path) :
    t.sourceTrail atoms overWord underWord (p++(childStep::q))=
      (t.sourceTrail atoms overWord underWord p).bind (fun before =>
        (child.sourceTrail atoms overWord underWord q).map (fun after => before++after)) := by
  rw [sourceTrail_split atoms overWord underWord lookup]
  have atRoot := sourceTrail_split atoms overWord underWord lookup []
  simp only [List.append_nil] at atRoot
  rw [atRoot]
  cases parent <;> cases childStep <;> simp only [subterm] at atChild
  all_goals cases atChild
  all_goals cases t.sourceStem atoms overWord underWord p <;>
    simp [sourceTrail,label,List.append_assoc,Function.comp_def]
end Lamping.Lambda.Labelled
