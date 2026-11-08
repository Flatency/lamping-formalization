import Lamping.Lamping.PlugLocalExcursions
import Lamping.Lamping.InitialPathConstruction
namespace Lamping.Checks.PlugLocalBlocks
open AG Graph
private abbrev F := Unit⊕Unit
private abbrev outside := wires F F (Bij.refl _)
private abbrev base := (Schema.croCancel 2).left
private abbrev middle := plug outside base
private abbrev shell := Context.empty.cons (.star .empty)
private abbrev input (tail : Context) := shell.replace 2 tail
private def basePath (tail : Context) : LocalPath base (.inl ()) (.inr ()) (input tail) (input tail) :=
  croCancelLeft 2 shell tail
private def middlePath (tail : Context) : LocalPath middle (.inl ()) (.inr ()) (input tail) (input tail) :=
  LocalPath.plugThree outside base
    (wirePath (Bij.refl F) (.inl ()) (input tail)) (basePath tail)
    (wirePath (Bij.refl F) (.inr ()) (input tail)).reverse
private def whole (tail : Context) :
    LocalPath (plug outside middle) (.inl ()) (.inr ()) (input tail) (input tail) :=
  LocalPath.plugThree outside middle
    (wirePath (Bij.refl F) (.inl ()) (input tail)) (middlePath tail)
    (wirePath (Bij.refl F) (.inr ()) (input tail)).reverse
private abbrev first : Endpoint outside := .inr (.inl (.inl (.inl ())))
private abbrev last : Endpoint outside := .inr (.inl (.inr (.inr ())))

-- The RHS contains two actual Cro nodes and two internal transparent glue
-- vertices. Its block is not a wire-only excursion.
example (tail : Context) : (middlePath tail).edges.length=5 := rfl
example (tail : Context) : (whole tail).edges.length=7 := rfl
example (tail : Context) :
    PlugExcursions outside middle ((whole tail).edges.map (plugEnd outside.label middle.label).invFun)
      (input tail) (input tail) :=
  (whole tail).labeling.local_excursions outside middle first last rfl rfl
example (tail : Context) :
    PlugLabelling outside middle ((whole tail).edges.map (plugEnd outside.label middle.label).invFun)
      (input tail) (input tail) :=
  ((whole tail).labeling.local_excursions outside middle first last rfl rfl).labelling outside middle
#print axioms PlugLabelling.right_first
#print axioms PlugLabelling.local_excursions
#print axioms PlugExcursions.labelling
end Lamping.Checks.PlugLocalBlocks
