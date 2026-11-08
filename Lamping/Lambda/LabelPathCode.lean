import Lamping.Lambda.LabelBoundaryAtoms
namespace Lamping.Lambda.Labelled

/-- Eight oriented turn kinds: direction and over/under determine a distinct
opening and closing turn. Atomic traversals retain their orientation. -/
inductive PathCodeToken where
  | edge : OrientedAtom → PathCodeToken
  | openTok : Bool → Bool → PathCodeToken
  | closeTok : Bool → Bool → PathCodeToken
  deriving DecidableEq, Repr

def Label.letters : Label → List Letter
  | .single l => [l]
  | .cons l a => l::a.letters

def lettersLabel : List Letter → Option Label
  | [] => none
  | [l] => some (.single l)
  | l::rest => (lettersLabel rest).map (.cons l)

theorem lettersLabel_letters : ∀ a : Label, lettersLabel a.letters=some a
  | .single _ => rfl
  | .cons l a => by
    cases a with
    | single q => rfl
    | cons q a =>
      change (lettersLabel (q::a.letters)).map (Label.cons l)=some _
      rw [show lettersLabel (q::a.letters)=some (.cons q a) from lettersLabel_letters (.cons q a)]
      rfl

theorem Label.letters_injective {a b : Label} (h : a.letters=b.letters) : a=b := by
  have eq := congrArg lettersLabel h
  simpa only [lettersLabel_letters,Option.some.injEq] using eq

def Label.traversalLetters (a : Label) (backwards : Bool) : List Letter :=
  if backwards then a.letters.reverse else a.letters

def traversalLabel (backwards : Bool) (letters : List Letter) : Option Label :=
  lettersLabel (if backwards then letters.reverse else letters)

theorem traversalLabel_letters (a : Label) (backwards : Bool) :
    traversalLabel backwards (a.traversalLetters backwards)=some a := by
  cases backwards <;> simp [traversalLabel,Label.traversalLetters,lettersLabel_letters]

mutual
  def Label.pathCode (backwards : Bool) : Label → List PathCodeToken
    | .single l => l.pathCode backwards
    | .cons l a => if backwards then a.pathCode backwards++l.pathCode backwards
        else l.pathCode backwards++a.pathCode backwards
  def Letter.pathCode (backwards : Bool) : Letter → List PathCodeToken
    | .atom n => [.edge ⟨n,backwards⟩]
    | .over a => .openTok backwards false :: (a.pathCode backwards++[.closeTok backwards false])
    | .under a => .openTok backwards true :: (a.pathCode (!backwards)++[.closeTok backwards true])
end

def CodeBoundary : List PathCodeToken → Prop
  | [] | .closeTok _ _ :: _ => True
  | _ => False

-- Word parsing may return any suffix; uniqueness requires a completed boundary.
mutual
  inductive CodeLetter : Bool → List PathCodeToken → Letter → List PathCodeToken → Prop where
    | atom : CodeLetter direction (.edge ⟨n,direction⟩::rest) (.atom n) rest
    | over : CodeWord direction input letters (.closeTok direction false::rest) →
        traversalLabel direction letters=some a →
        CodeLetter direction (.openTok direction false::input) (.over a) rest
    | under : CodeWord (!direction) input letters (.closeTok direction true::rest) →
        traversalLabel (!direction) letters=some a →
        CodeLetter direction (.openTok direction true::input) (.under a) rest
  inductive CodeWord : Bool → List PathCodeToken → List Letter → List PathCodeToken → Prop where
    | nil : CodeWord direction rest [] rest
    | cons : CodeLetter direction input l middle → CodeWord direction middle ls rest →
        CodeWord direction input (l::ls) rest
end

theorem CodeWord.append (h : CodeWord direction input ls middle)
    (k : CodeWord direction middle ms rest) : CodeWord direction input (ls++ms) rest := by
  refine CodeWord.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun d inp ls mid _ => ∀ {ms rest}, CodeWord d mid ms rest → CodeWord d inp (ls++ms) rest)
    ?_ ?_ ?_ ?_ ?_ h k
  · intro direction n rest; trivial
  · intro direction inp letters rest a word value ih; trivial
  · intro direction inp letters rest a word value ih; trivial
  · intro direction rest ms finish k; exact k
  · intro direction inp l mid ls finish letter word _ ih ms rest k
    exact .cons letter (ih k)

theorem CodeLetter.not_boundary (h : CodeLetter direction input l rest) : ¬ CodeBoundary input := by
  cases h <;> exact id

theorem CodeWord.deterministic (h : CodeWord direction input ls rest)
    (k : CodeWord direction input ls' rest') (stop : CodeBoundary rest) (stop' : CodeBoundary rest') :
    ls=ls' ∧ rest=rest' := by
  refine CodeWord.rec
    (motive_1 := fun d inp l finish _ => ∀ {l' finish'}, CodeLetter d inp l' finish' → l=l' ∧ finish=finish')
    (motive_2 := fun d inp ls finish _ => ∀ {ls' finish'}, CodeWord d inp ls' finish' →
      CodeBoundary finish → CodeBoundary finish' → ls=ls' ∧ finish=finish')
    ?_ ?_ ?_ ?_ ?_ h k stop stop'
  · intro direction n rest l' rest' k
    cases k; exact ⟨rfl,rfl⟩
  · intro direction inp letters rest a word value ih l' rest' k
    cases k with
    | over word' value' =>
      obtain ⟨lettersEq,finish⟩ := ih word' True.intro True.intro
      cases lettersEq; cases finish
      have eq := Option.some.inj (value.symm.trans value')
      cases eq; exact ⟨rfl,rfl⟩
  · intro direction inp letters rest a word value ih l' rest' k
    cases k with
    | under word' value' =>
      obtain ⟨lettersEq,finish⟩ := ih word' True.intro True.intro
      cases lettersEq; cases finish
      have eq := Option.some.inj (value.symm.trans value')
      cases eq; exact ⟨rfl,rfl⟩
  · intro direction rest ls' rest' k stop stop'
    cases k with
    | nil => exact ⟨rfl,rfl⟩
    | cons letter _ => exact False.elim (letter.not_boundary stop)
  · intro direction inp l middle ls rest letter word ihl ihw ls' rest' k stop stop'
    cases k with
    | nil => exact False.elim (letter.not_boundary stop')
    | cons letter' word' =>
      obtain ⟨head,middleEq⟩ := ihl letter'
      cases head; cases middleEq
      obtain ⟨tail,finish⟩ := ihw word' stop stop'
      cases tail; exact ⟨rfl,finish⟩

mutual
  theorem Label.parse_pathCode (a : Label) (direction : Bool) (suffix : List PathCodeToken) :
      CodeWord direction (a.pathCode direction++suffix) (a.traversalLetters direction) suffix := by
    cases a with
    | single l =>
      cases direction <;> exact .cons (Letter.parse_pathCode _ _ _) (.nil)
    | cons l a =>
      cases direction with
      | false =>
        simpa only [Label.pathCode,Bool.false_eq_true,ite_false,Label.traversalLetters,Label.letters,
          List.append_assoc] using
          (CodeWord.cons (Letter.parse_pathCode l false (a.pathCode false++suffix))
            (Label.parse_pathCode a false suffix))
      | true =>
        simpa only [Label.pathCode,ite_true,Label.traversalLetters,Label.letters,List.reverse_cons,
          List.append_assoc] using
          ((Label.parse_pathCode a true (l.pathCode true++suffix)).append
            (CodeWord.cons (Letter.parse_pathCode l true suffix) (.nil)))
  theorem Letter.parse_pathCode (l : Letter) (direction : Bool) (suffix : List PathCodeToken) :
      CodeLetter direction (l.pathCode direction++suffix) l suffix := by
    cases l with
    | atom => exact .atom
    | over a =>
      simpa only [Letter.pathCode,List.cons_append,List.append_assoc,List.singleton_append] using
        (CodeLetter.over (Label.parse_pathCode a direction (.closeTok direction false::suffix))
          (traversalLabel_letters a direction))
    | under a =>
      simpa only [Letter.pathCode,List.cons_append,List.append_assoc,List.singleton_append] using
        (CodeLetter.under (Label.parse_pathCode a (!direction) (.closeTok direction true::suffix))
          (traversalLabel_letters a (!direction)))
end

/-- Bar structure is uniquely recoverable when the directed turn code is
retained. Recovering this code from edgeWord is a separate geometric theorem. -/
theorem Label.pathCode_injective (direction : Bool) {a b : Label}
    (h : a.pathCode direction=b.pathCode direction) : a=b := by
  have pa := a.parse_pathCode direction []
  have pb := b.parse_pathCode direction []
  simp only [List.append_nil] at pa pb
  rw [h] at pa
  obtain ⟨same,_⟩ := CodeWord.deterministic pa pb True.intro True.intro
  cases direction with
  | false => exact Label.letters_injective same
  | true =>
    apply Label.letters_injective
    have reversed := congrArg List.reverse same
    simpa only [Label.traversalLetters,ite_true,List.reverse_reverse] using reversed
end Lamping.Lambda.Labelled
