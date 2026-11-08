import Lamping.Lambda.DirectedFreshMarkerParsing
namespace Lamping.Checks.DirectedFreshMarkerParsing
open Lambda Lambda.Labelled

private abbrev a := Label.atom
private abbrev identity (n : Nat) : LTerm := .lam (a n) (.var (a (n+1)) 0)
private abbrev inner : LTerm := .app (a 0) (.lam (a 1) (.var (a 2) 0)) (identity 3)
private abbrev result := LTerm.contract (a 0) (a 1) (.var (a 2) 0) (identity 3)
private abbrev source : LTerm := .app (a 5) inner (identity 6)
private abbrev target : LTerm := .app (a 5) result (identity 6)
private def turn : StepAt [.fn] source target := .fn (.root _ _ _ _)
private def functionOrigin : BetaIncomingReadingOrigin (.var (a 2) 0) (identity 3)
    [.fn] [.fn] [] [] [.fn] [.fn,.fn,.body] := .resultFunction rfl rfl
private def lambdaOrigin : BetaIncomingReadingOrigin (.var (a 2) 0) (identity 3)
    [.fn] [.fn] [.fn] [.fn,.arg] [.fn,.arg] [.fn,.fn,.body] :=
  .copyLambda (q:=[]) rfl rfl rfl rfl

theorem actual_init_turn : INIT source ∧StepAt [.fn] source target := by
  exact ⟨by simp [INIT,LTerm.labels,IsAtomic,a,Label.atom],turn⟩

/-- Both FUNCTION and lambda CONTEXT use actual creation-origin equations.
An arbitrary competing safe first-marker split has the same label, marker,
and whole suffix. This does not identify syntax positions by their labels. -/
theorem actual_directed_unique (forward : Bool) :
    ∃ first last marker tail,
      source.subterm (if forward then [.fn] else [.fn,.arg])=some first ∧
      source.subterm [.fn,.fn,.body]=some last ∧marker.MarksDegree (a 1) ∧
      result.label.readLetters forward=first.label.readLetters forward++marker::tail ∧
      ∀ other next rest,
        other.OuterBarsSafe (fun x=>x≠a 1) →next.MarksDegree (a 1) →
        result.label.readLetters forward=other.readLetters forward++next::rest →
        first.label=other ∧marker=next ∧tail=rest := by
  have created : ∃ first last marker tail,
      source.subterm (if forward then [.fn] else [.fn,.arg])=some first ∧
      source.subterm [.fn,.fn,.body]=some last ∧marker.MarksDegree (a 1) ∧
      result.label.readLetters forward=first.label.readLetters forward++marker::tail := by
    cases forward with
    | true =>
      exact functionOrigin.directed_label_prefix turn rfl
        ⟨Or.inl ⟨_,_,_,rfl,rfl⟩,rfl⟩ rfl
    | false =>
      exact lambdaOrigin.directed_label_prefix turn rfl
        ⟨Or.inr ⟨_,_,rfl,rfl⟩,rfl⟩ rfl
  obtain ⟨first,last,marker,tail,firstAt,lastAt,marked,equation⟩ := created
  have sourceSafe : source.OuterBarsSafe (fun x=>x≠a 1) := by
    simp [a,Label.atom,LTerm.OuterBarsSafe,Label.OuterBarsSafe]
  have firstSafe := (LTerm.outerBarsSafe_iff _ _).mp sourceSafe _ (LTerm.label_mem_of_subterm firstAt)
  refine ⟨first,last,marker,tail,firstAt,lastAt,marked,equation,?_⟩
  intro other next rest safe markedNext alternative
  exact Label.readLetters_first_marker_of_splits firstSafe safe marked markedNext
    equation alternative rfl

/-- Empty tails cannot be represented by Label. The word interface covers
them in either direction, and returns the literal empty tail. -/
theorem empty_tail (forward : Bool) {other : Label} {next : Letter} {rest : List Letter}
    (safe : other.OuterBarsSafe (fun x=>x≠a 1)) (marked : next.MarksDegree (a 1))
    (same : (a 0).readLetters forward++[.over (a 1)]=other.readLetters forward++next::rest) :
    a 0=other ∧.over (a 1)=next ∧rest=[] := by
  have beforeSafe : (a 0).OuterBarsSafe (fun x=>x≠a 1) := by
    simp [a,Label.atom,Label.OuterBarsSafe]
  obtain ⟨first,marker,tail⟩ := Label.readLetters_first_marker_unique
    beforeSafe safe (Or.inl rfl) marked same
  exact ⟨first,marker,tail.symm⟩

/-- The real result/copy overlap has two markers. The reverse reading's
first marker is under; it cannot be mistaken for a later over marker. -/
theorem actual_reverse_first_under :
    result.label.readLetters false=[.atom 3,.under (a 1),.atom 2,.over (a 1),.atom 0] ∧
    ∀ tail,result.label.readLetters false≠[.atom 3]++(.over (a 1))::tail := by
  refine ⟨rfl,?_⟩
  intro tail impossible
  have different := (List.cons.inj (List.cons.inj impossible).2).1
  cases different

#print axioms Label.readLetters_first_marker_unique
#print axioms Label.readLetters_first_marker_of_splits
#print axioms actual_directed_unique
#print axioms empty_tail
#print axioms actual_reverse_first_under
end Lamping.Checks.DirectedFreshMarkerParsing
