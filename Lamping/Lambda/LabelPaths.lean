import Lamping.Lambda.LabelRelabelling
namespace Lamping.Lambda.Labelled

/-- A traversal of an original atomic edge, including its orientation. -/
structure OrientedAtom where
  atom : Nat
  backwards : Bool
  deriving DecidableEq, Repr

def OrientedAtom.flip (e : OrientedAtom) : OrientedAtom := ⟨e.atom,!e.backwards⟩
@[simp] theorem OrientedAtom.flip_flip (e : OrientedAtom) : e.flip.flip=e := by
  cases e with | mk n b => cases b <;> rfl

abbrev EdgeWord := List OrientedAtom

def EdgeWord.reverse (p : EdgeWord) : EdgeWord := (List.reverse p).map OrientedAtom.flip

theorem EdgeWord.reverse_append (p q : EdgeWord) :
    EdgeWord.reverse (p++q)=EdgeWord.reverse q++EdgeWord.reverse p := by
  simp [EdgeWord.reverse,List.reverse_append,List.map_append]

@[simp] theorem EdgeWord.reverse_reverse (p : EdgeWord) :
    EdgeWord.reverse (EdgeWord.reverse p)=p := by
  simp [EdgeWord.reverse,List.map_reverse,List.map_map,Function.comp_def]

mutual
  def Label.edgeWord : Label → EdgeWord
    | .single l => l.edgeWord
    | .cons l a => l.edgeWord++a.edgeWord
  def Letter.edgeWord : Letter → EdgeWord
    | .atom n => [⟨n,false⟩]
    | .over a => a.edgeWord
    | .under a => EdgeWord.reverse a.edgeWord
end

@[simp] theorem Label.edgeWord_atom (n) : (Label.atom n).edgeWord=[⟨n,false⟩] := rfl
@[simp] theorem Label.edgeWord_over (a : Label) : a.over.edgeWord=a.edgeWord := rfl
@[simp] theorem Label.edgeWord_under (a : Label) : a.under.edgeWord=EdgeWord.reverse a.edgeWord := rfl

theorem Label.edgeWord_concat : ∀ (a b : Label), (a.concat b).edgeWord=a.edgeWord++b.edgeWord
  | .single _,_ => rfl
  | .cons _ a,b => by simp [Label.concat,Label.edgeWord,edgeWord_concat,List.append_assoc]

/-- Oriented edge substitution reverses both order and orientation for a
backwards edge, as required by AG Exercise6.2.14's warning. -/
def EdgeWord.substitute (s : Nat → EdgeWord) (p : EdgeWord) : EdgeWord :=
  p.flatMap (fun e => if e.backwards then EdgeWord.reverse (s e.atom) else s e.atom)

theorem EdgeWord.substitute_append (s) (p q : EdgeWord) :
    EdgeWord.substitute s (p++q)=EdgeWord.substitute s p++EdgeWord.substitute s q := by
  simp [EdgeWord.substitute,List.flatMap_append]

theorem EdgeWord.substitute_reverse (s) (p : EdgeWord) :
    EdgeWord.substitute s (EdgeWord.reverse p)=EdgeWord.reverse (EdgeWord.substitute s p) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    rw [show e::p=[e]++p from rfl,EdgeWord.reverse_append,EdgeWord.substitute_append,
      EdgeWord.substitute_append,EdgeWord.reverse_append,ih]
    congr 1
    cases e with | mk n b => cases b <;> simp [EdgeWord.substitute,EdgeWord.reverse,OrientedAtom.flip,Function.comp_def]

mutual
  theorem Label.edgeWord_relabel (s) : ∀ a : Label,
      (a.relabel s).edgeWord=EdgeWord.substitute (fun n => (s n).edgeWord) a.edgeWord
    | .single l => by simpa [Label.relabel,Label.edgeWord] using Letter.edgeWord_relabel s l
    | .cons l a => by simp [Label.relabel,Label.edgeWord_concat,Label.edgeWord,
        EdgeWord.substitute_append,Letter.edgeWord_relabel,Label.edgeWord_relabel]
  theorem Letter.edgeWord_relabel (s) : ∀ l : Letter,
      (l.relabel s).edgeWord=EdgeWord.substitute (fun n => (s n).edgeWord) l.edgeWord
    | .atom n => by simp [Letter.relabel,Letter.edgeWord,EdgeWord.substitute]
    | .over a => by simp [Letter.relabel,Letter.edgeWord,Label.edgeWord_relabel]
    | .under a => by simp [Letter.relabel,Letter.edgeWord,Label.edgeWord_relabel,EdgeWord.substitute_reverse]
end

/-- The path function is deliberately not claimed injective on arbitrary
labels: injectivity in AG6.2.8 requires the generated-label geometry. -/
theorem arbitrary_edgeWord_not_injective :
    ¬ Function.Injective Label.edgeWord := by
  intro h
  have wrong := h (show (Label.atom 0).edgeWord=(Label.atom 0).over.edgeWord from rfl)
  cases wrong

end Lamping.Lambda.Labelled



