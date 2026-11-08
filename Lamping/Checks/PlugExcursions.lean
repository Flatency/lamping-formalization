import Lamping.Lamping.WireRhsExcursions
namespace Lamping.Checks.PlugExcursions
open AG Graph
private abbrev F := Bool×Bool
private def outside : Net signature Empty (Bool⊕F) Empty where
  label := Empty.elim
  wire := {
    mate := fun e => match e with
      | .inl ⟨node,_⟩ => nomatch node
      | .inr (.inr (w,_)) => nomatch w
      | .inr (.inl (.inl false)) => .inr (.inl (.inr (false,false)))
      | .inr (.inl (.inl true)) => .inr (.inl (.inr (true,true)))
      | .inr (.inl (.inr (false,false))) => .inr (.inl (.inl false))
      | .inr (.inl (.inr (false,true))) => .inr (.inl (.inr (true,false)))
      | .inr (.inl (.inr (true,false))) => .inr (.inl (.inr (false,true)))
      | .inr (.inl (.inr (true,true))) => .inr (.inl (.inl true))
    involutive := by
      rintro (⟨node,_⟩ | ((b|⟨a,b⟩) | ⟨w,d⟩))
      · exact nomatch node
      · cases b <;> rfl
      · cases a <;> cases b <;> rfl
      · exact nomatch w
    fixedPointFree := by
      rintro (⟨node,_⟩ | ((b|⟨a,b⟩) | ⟨w,d⟩)) same
      · exact nomatch node
      · cases b <;> cases same
      · cases a <;> cases b <;> cases same
      · exact nomatch w }
private def rhs : Net signature Empty F Empty where
  label := Empty.elim
  wire := {
    mate := fun e => match e with
      | .inl ⟨node,_⟩ => nomatch node
      | .inr (.inr (w,_)) => nomatch w
      | .inr (.inl (a,b)) => .inr (.inl (a,!b))
    involutive := by
      rintro (⟨node,_⟩ | (⟨a,b⟩ | ⟨w,d⟩))
      · exact nomatch node
      · cases b <;> rfl
      · exact nomatch w
    fixedPointFree := by
      rintro (⟨node,_⟩ | (⟨a,b⟩ | ⟨w,d⟩)) same
      · exact nomatch node
      · cases b <;> cases same
      · exact nomatch w }

private abbrev root : Endpoint outside := .inr (.inl (.inl false))
private abbrev frontier (f : F) : Endpoint outside := .inr (.inl (.inr f))
private abbrev inside (f : F) : Endpoint rhs := .inr (.inl f)
private def raw : List (PlugSegment outside rhs) :=
  [.inl root,.inr (inside (false,false)),.inl (frontier (false,true)),
    .inr (inside (true,false)),.inl (frontier (true,true))]
private theorem raw_labels (a : Context) : PlugLabelling outside rhs raw a a :=
  .cons (.enter (false,false) a) (.cons (.leave (false,true) a)
    (.cons (.enter (true,false) a) (.cons (.leave (true,true) a) (.single _ _))))

-- The external pairing joins two different frontier occurrences. Actual
-- labels still yield two consecutive ordered RHS excursions, not a set.
example (a : Context) : WireExcursions outside rhs raw a a :=
  (raw_labels a).wire_excursions outside rhs root (frontier (true,true)) rfl rfl
example (a : Context) : Labelling (plug outside rhs) (raw.map (plugEnd outside.label rhs.label)) a a :=
  (raw_labels a).actual outside rhs
example : raw.length=5 := rfl
example (a : Context) : WireExcursions outside rhs [.inl root] a a :=
  (PlugLabelling.single (c:=outside) (r:=rhs) (.inl root) a).wire_excursions outside rhs root root rfl rfl
example (a : Context) : PlugLabelling outside rhs [.inl root,.inr (inside (false,false))] a a :=
  .cons (.enter (false,false) a) (.single _ _)
example (a b : Context) : ¬WireExcursions outside rhs [.inl root,.inr (inside (false,false))] a b := by
  intro path
  cases path
#print axioms Labelling.plug_decomposition
#print axioms PlugLabelling.wire_excursions
end Lamping.Checks.PlugExcursions
