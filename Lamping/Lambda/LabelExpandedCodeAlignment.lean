import Lamping.Lambda.LabelHeadMarkerParsing
namespace Lamping.Lambda.Labelled

abbrev ExpandedCodeToken := Sum (Label × Bool) PathCodeToken

def PathCodeToken.imageToken (s : Nat → Label) : PathCodeToken → ExpandedCodeToken
  | .edge e => .inl (s e.atom,e.backwards)
  | token => .inr token

def Label.imageCode (s : Nat → Label) (direction : Bool) (l : Label) : List ExpandedCodeToken :=
  (l.pathCode direction).map (PathCodeToken.imageToken s)

def Letter.imageCode (s : Nat → Label) (direction : Bool) (l : Letter) : List ExpandedCodeToken :=
  (l.pathCode direction).map (PathCodeToken.imageToken s)

def Letter.expansionToken (s : Nat → Label) : Letter → Sum (List Letter) Letter
  | .atom n => .inl (s n).letters
  | .over d => .inr (.over (d.relabel s))
  | .under d => .inr (.under (d.relabel s))

private theorem Label.pathCode_letters : ∀ (l : Label) (direction : Bool),
    l.pathCode direction=(l.traversalLetters direction).flatMap (fun letter => letter.pathCode direction)
  | .single letter,direction => by cases direction <;> simp [Label.pathCode,Label.traversalLetters,Label.letters]
  | .cons letter rest,false => by
    simp only [Label.pathCode,Bool.false_eq_true,ite_false,Label.traversalLetters,Label.letters,List.flatMap_cons]
    rw [Label.pathCode_letters rest false]
    rfl
  | .cons letter rest,true => by
    simp only [Label.pathCode,ite_true,Label.traversalLetters,Label.letters,List.reverse_cons,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [Label.pathCode_letters rest true]
    rfl

theorem Label.imageCode_letters (s) (direction) (l : Label) :
    l.imageCode s direction=(l.traversalLetters direction).flatMap (fun letter => letter.imageCode s direction) := by
  simp only [Label.imageCode,Label.pathCode_letters,List.map_flatMap,Letter.imageCode]
private theorem Label.supported_letters : ∀ {l : Label},l.Supported region → ∀ letter∈l.letters,letter.Supported region
  | .single _,support,letter,member => by simp only [Label.letters,List.mem_singleton] at member; cases member; exact support
  | .cons first rest,support,letter,member => by
    rcases List.mem_cons.mp member with equal | inside
    · exact equal ▸ support.1
    · exact Label.supported_letters support.2 letter inside

private def Letter.PayloadAlternating : Letter → Prop
  | .atom _ => True
  | .over d | .under d => d.Alternating

private theorem Label.Alternating.payloads {l : Label} (alternating : l.Alternating) :
    ∀ letter∈l.letters,letter.PayloadAlternating := by
  induction alternating with
  | atom n => intro letter member; simp only [Label.atom,Label.letters,List.mem_singleton] at member; cases member; trivial
  | over left middle right hl hm hr =>
    intro letter member
    simp only [Label.letters_concat,Label.over,Label.letters,List.mem_append,List.mem_singleton] at member
    rcases member with (inside | equal) | inside
    · exact hl letter inside
    · cases equal; exact middle
    · exact hr letter inside
  | under left middle right hl hm hr =>
    intro letter member
    simp only [Label.letters_concat,Label.under,Label.letters,List.mem_append,List.mem_singleton] at member
    rcases member with (inside | equal) | inside
    · exact hl letter inside
    · cases equal; exact middle
    · exact hr letter inside

private theorem Label.letter_size : ∀ {l : Label} {letter},letter∈l.letters → sizeOf letter<sizeOf l
  | .single first,letter,member => by
    simp only [Label.letters,List.mem_singleton] at member
    cases member
    simp
  | .cons first rest,letter,member => by
    rcases List.mem_cons.mp member with equal | inside
    · cases equal; simp; omega
    · have smaller := Label.letter_size inside
      simp at *
      omega

private inductive WordPairs (R : α → β → Prop) : List α → List β → Prop where
  | nil : WordPairs R [] []
  | cons : R x y → WordPairs R xs ys → WordPairs R (x::xs) (y::ys)

private theorem paired_of_map_eq {R : α → β → Prop} {xs : List α} {ys : List β} {f : α → γ} {g : β → γ}
    (equal : xs.map f=ys.map g)
    (point : ∀ x∈xs,∀ y∈ys,f x=g y → R x y) : WordPairs R xs ys := by
  induction xs generalizing ys with
  | nil => cases ys with | nil => exact .nil | cons y ys => cases equal
  | cons x xs ih =>
    cases ys with
    | nil => cases equal
    | cons y ys =>
      have pair := List.cons.inj equal
      exact .cons (point x List.mem_cons_self y List.mem_cons_self pair.1)
        (ih pair.2 (fun a ha b hb eq => point a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) eq))

private theorem flatMap_eq_of_paired {xs : List α} {ys : List β} {f : α → List γ} {g : β → List γ} (pairs : WordPairs (fun x y => f x=g y) xs ys) :
    xs.flatMap f=ys.flatMap g := by
  induction pairs with
  | nil => rfl
  | cons equal rest ih => simp only [List.flatMap_cons,equal,ih]

private theorem WordPairs.imp (pairs : WordPairs R xs ys) (point : ∀ {x y},R x y → S x y) : WordPairs S xs ys := by
  induction pairs with
  | nil => exact .nil
  | cons equal rest ih => exact .cons (point equal) ih

private theorem WordPairs.append (left : WordPairs R xs ys) (right : WordPairs R zs ws) :
    WordPairs R (xs++zs) (ys++ws) := by
  induction left with
  | nil => exact right
  | cons first rest ih => exact .cons first ih

private theorem WordPairs.reverse (pairs : WordPairs R xs ys) : WordPairs R xs.reverse ys.reverse := by
  induction pairs with
  | nil => exact .nil
  | cons equal rest ih => simpa only [List.reverse_cons] using ih.append (.cons equal .nil)

private theorem all_code_alignment {region : Nat → Prop} {s : Nat → Label}
    (images : ∀ n,region n → (s n).HeadFlat a) : ∀ weight,∀ {left right : Label},sizeOf left=weight →
      left.Alternating → right.Alternating → left.Supported region → right.Supported region →
      left.relabel s=right.relabel s → ∀ direction,left.imageCode s direction=right.imageCode s direction := by
  intro weight
  induction weight using Nat.strongRecOn with
  | ind weight ih =>
    intro left right sizeEq leftAlt rightAlt leftSupport rightSupport same
    have parsedLeft := leftAlt.relabel_headGroups images leftSupport
    have parsedRight := rightAlt.relabel_headGroups images rightSupport
    have tokens : left.letters.map (Letter.expansionToken s)=right.letters.map (Letter.expansionToken s) :=
      parsedLeft.symm.trans ((congrArg (fun label => headGroups a label.letters) same).trans parsedRight)
    have pairs : WordPairs (fun x y : Letter => ∀ direction,x.imageCode s direction=y.imageCode s direction)
        left.letters right.letters := by
      apply paired_of_map_eq tokens
      intro x xMember y yMember equal
      cases x with
      | atom n =>
        cases y with
        | atom m =>
          have imageEq := Label.letters_injective (Sum.inl.inj equal)
          intro direction
          cases direction <;> simp [Letter.imageCode,Letter.pathCode,PathCodeToken.imageToken,imageEq]
        | over d => cases equal
        | under d => cases equal
      | over d =>
        cases y with
        | atom m => cases equal
        | under e => cases equal
        | over e =>
          have payloadSame : d.relabel s=e.relabel s := Letter.over.inj (Sum.inr.inj equal)
          have bound := Label.letter_size xMember
          have smaller : sizeOf d<weight := by simp at bound; omega
          have recurse := ih (sizeOf d) smaller rfl (leftAlt.payloads _ xMember) (rightAlt.payloads _ yMember)
            (Label.supported_letters leftSupport _ xMember) (Label.supported_letters rightSupport _ yMember) payloadSame
          intro direction
          simp only [Letter.imageCode,Letter.pathCode,List.map_cons,List.map_append,List.map_nil,PathCodeToken.imageToken]
          change Sum.inr (.openTok direction false)::(d.imageCode s direction++[Sum.inr (.closeTok direction false)])=
            Sum.inr (.openTok direction false)::(e.imageCode s direction++[Sum.inr (.closeTok direction false)])
          rw [recurse direction]
      | under d =>
        cases y with
        | atom m => cases equal
        | over e => cases equal
        | under e =>
          have payloadSame : d.relabel s=e.relabel s := Letter.under.inj (Sum.inr.inj equal)
          have bound := Label.letter_size xMember
          have smaller : sizeOf d<weight := by simp at bound; omega
          have recurse := ih (sizeOf d) smaller rfl (leftAlt.payloads _ xMember) (rightAlt.payloads _ yMember)
            (Label.supported_letters leftSupport _ xMember) (Label.supported_letters rightSupport _ yMember) payloadSame
          intro direction
          simp only [Letter.imageCode,Letter.pathCode,List.map_cons,List.map_append,List.map_nil,PathCodeToken.imageToken]
          change Sum.inr (.openTok direction true)::(d.imageCode s (!direction)++[Sum.inr (.closeTok direction true)])=
            Sum.inr (.openTok direction true)::(e.imageCode s (!direction)++[Sum.inr (.closeTok direction true)])
          rw [recurse (!direction)]
    intro direction
    rw [Label.imageCode_letters,Label.imageCode_letters]
    cases direction with
    | false => exact flatMap_eq_of_paired (pairs.imp (fun point => point false))
    | true => exact flatMap_eq_of_paired (pairs.reverse.imp (fun point => point true))

/-- Recover the entire ordered signed local code, including every nested
payload and its under reversal, with whole edge images retained as atoms.
Equal image atoms are still permitted to denote different argument copies. -/
theorem Label.Alternating.relabel_imageCode {left right : Label} {region : Nat → Prop} {s : Nat → Label}
    (leftAlt : left.Alternating) (rightAlt : right.Alternating)
    (images : ∀ n,region n → (s n).HeadFlat a)
    (leftSupport : left.Supported region) (rightSupport : right.Supported region)
    (same : left.relabel s=right.relabel s) (direction : Bool) :
    left.imageCode s direction=right.imageCode s direction :=
  all_code_alignment images (sizeOf left) rfl leftAlt rightAlt leftSupport rightSupport same direction
/-- The full signed-code alignment for two actual tails after the same real
beta step. The original global labelling stays fixed throughout. -/
theorem StepAt.same_degree_imageCode (head : StepAt p t u) (initial : INIT t)
    (headDegree : t.degreeAt p=some (Label.atom a))
    (left : History ps u v) (leftBasis : History ps (initLabels u.erase) z)
    (right : History qs u w) (rightBasis : History qs (initLabels u.erase) z')
    (leftDegree : v.degreeAt q=some l) (leftLocal : z.degreeAt q=some localLeft)
    (rightDegree : w.degreeAt r=some l) (rightLocal : z'.degreeAt r=some localRight) (direction : Bool) :
    localLeft.imageCode (initialRelabelling u 0) direction=localRight.imageCode (initialRelabelling u 0) direction := by
  obtain ⟨leftBody,leftLookup⟩ := LTerm.degreeAt_lambda leftLocal
  obtain ⟨rightBody,rightLookup⟩ := LTerm.degreeAt_lambda rightLocal
  have leftMember := LTerm.label_mem_of_subterm leftLookup
  have rightMember := LTerm.label_mem_of_subterm rightLookup
  have leftAlt := leftBasis.generated_label_alternating (init_is_INIT _) leftMember
  have rightAlt := rightBasis.generated_label_alternating (init_is_INIT _) rightMember
  have leftSupport := (LTerm.supported_iff _ _).mp (leftBasis.supported (init_is_INIT _).supported) _ leftMember
  have rightSupport := (LTerm.supported_iff _ _).mp (rightBasis.supported (init_is_INIT _).supported) _ rightMember
  have images : ∀ n,Label.atom n∈(initLabels u.erase).labels → (initialRelabelling u 0 n).HeadFlat a :=
    fun n member => head.basis_images_headFlat initial headDegree member
  have leftEq := Option.some.inj ((left.local_degree_transport leftBasis leftLocal).1.symm.trans leftDegree)
  have rightEq := Option.some.inj ((right.local_degree_transport rightBasis rightLocal).1.symm.trans rightDegree)
  exact leftAlt.relabel_imageCode rightAlt images leftSupport rightSupport (leftEq.trans rightEq.symm) direction
end Lamping.Lambda.Labelled





