import Lamping.Lambda.UniformOldOuterImageAlignment
import Lamping.Lambda.DirectedReadingCreation

namespace Lamping.Lambda.Labelled

variable {label labelLeft labelRight left right : Label} {forward : Bool}

def readingBar (over : Bool) (degree : Label) : Letter :=
  if over then .over degree else .under degree

inductive PairedDirectedCellShape :
    List Letter → List Letter → List Letter → List Letter → Type where
  | singleton : PairedDirectedCellShape [] [] [] []
  | first (kind : Bool) (leftDegree rightDegree : Label)
      (leftRest rightRest : List Letter) :
      PairedDirectedCellShape [] [] (readingBar kind leftDegree::leftRest)
        (readingBar kind rightDegree::rightRest)
  | last (kind : Bool) (leftDegree rightDegree : Label)
      (leftBefore rightBefore : List Letter) :
      PairedDirectedCellShape (leftBefore++[readingBar kind leftDegree])
        (rightBefore++[readingBar kind rightDegree]) [] []
  | interior (nearKind farKind : Bool) (leftNear rightNear leftFar rightFar : Label)
      (leftBefore rightBefore leftAfter rightAfter : List Letter) :
      PairedDirectedCellShape (leftBefore++[readingBar nearKind leftNear])
        (rightBefore++[readingBar nearKind rightNear])
        (readingBar farKind leftFar::leftAfter) (readingBar farKind rightFar::rightAfter)

structure PairedDirectedAtomCell (s : Nat → Label) (leftWord rightWord : List Letter)
    (leftBefore : List Letter) (leftAtom : Nat) (leftAfter : List Letter) where
  rightAtom : Nat
  rightBefore : List Letter
  rightAfter : List Letter
  leftSplit : leftWord=leftBefore++(.atom leftAtom::leftAfter)
  rightSplit : rightWord=rightBefore++(.atom rightAtom::rightAfter)
  beforeLength : leftBefore.length=rightBefore.length
  afterLength : leftAfter.length=rightAfter.length
  rightBeforeCanonical : rightBefore=rightWord.take leftBefore.length
  rightAfterCanonical : rightAfter=rightWord.drop (leftBefore.length+1)
  fullImageEq : s leftAtom=s rightAtom
  beforeKeys : leftBefore.map (Letter.outerImageKey s)=rightBefore.map (Letter.outerImageKey s)
  afterKeys : leftAfter.map (Letter.outerImageKey s)=rightAfter.map (Letter.outerImageKey s)
  shape : PairedDirectedCellShape leftBefore rightBefore leftAfter rightAfter

structure DirectedOuterAtomCells (s : Nat → Label) (left right : Label) (forward : Bool) where
  leftAlternating : left.Alternating
  rightAlternating : right.Alternating
  keyEq : (left.readLetters forward).map (Letter.outerImageKey s)=
    (right.readLetters forward).map (Letter.outerImageKey s)
  lengthEq : (left.readLetters forward).length=(right.readLetters forward).length
  leftCells : ∀ pre n post, left.readLetters forward=pre++(.atom n::post) →
    Nonempty (PairedDirectedAtomCell s (left.readLetters forward) (right.readLetters forward) pre n post)
  rightCells : ∀ pre n post, right.readLetters forward=pre++(.atom n::post) →
    Nonempty (PairedDirectedAtomCell s (right.readLetters forward) (left.readLetters forward) pre n post)

private inductive AtomBarWord : List Letter → Prop where
  | last (n : Nat) : AtomBarWord [.atom n]
  | next (n : Nat) (kind : Bool) (degree : Label) (tail : List Letter) :
      AtomBarWord tail → AtomBarWord (.atom n::readingBar kind degree::tail)

private theorem AtomBarWord.join (hx : AtomBarWord xs) (hy : AtomBarWord ys)
    (kind : Bool) (degree : Label) : AtomBarWord (xs++readingBar kind degree::ys) := by
  induction hx with
  | last n => exact .next n kind degree _ hy
  | next n k d tail h ih => exact .next n k d _ ih

private theorem AtomBarWord.reverse (h : AtomBarWord xs) : AtomBarWord xs.reverse := by
  induction h with
  | last n => exact .last n
  | next n k d tail h ih =>
      simpa only [List.reverse_cons, List.append_assoc] using
        ih.join (.last n) k d

private theorem Label.Alternating.atomBarWord (h : label.Alternating) :
    AtomBarWord label.letters := by
  induction h with
  | atom n => exact .last n
  | @over a d b ha hd hb ia id ib =>
      simpa [Label.letters_concat,Label.over,Label.letters,readingBar,List.append_assoc] using ia.join ib true d
  | @under a d b ha hd hb ia id ib =>
      simpa [Label.letters_concat,Label.under,Label.letters,readingBar,List.append_assoc] using ia.join ib false d

private theorem Label.Alternating.readAtomBarWord (h : label.Alternating) (forward : Bool) :
    AtomBarWord (label.readLetters forward) := by
  cases forward
  · exact h.atomBarWord.reverse
  · exact h.atomBarWord

private theorem AtomBarWord.neighbors (h : AtomBarWord xs)
    (split : xs=pre++(.atom n::post)) :
    (pre=[] ∨ ∃ front kind degree, pre=front++[readingBar kind degree]) ∧
    (post=[] ∨ ∃ kind degree suffix, post=readingBar kind degree::suffix) := by
  induction h generalizing pre n post with
  | last m =>
      have len := congrArg List.length split
      simp only [List.length_append, List.length_cons,List.length_nil] at len
      have hp : pre=[] := List.length_eq_zero_iff.mp (by omega)
      have ht : post=[] := List.length_eq_zero_iff.mp (by omega)
      exact ⟨.inl hp,.inl ht⟩
  | next m k d tail h ih =>
      cases pre with
      | nil =>
          have e := List.cons.inj split
          exact ⟨.inl rfl,.inr ⟨k,d,tail,e.2.symm⟩⟩
      | cons a pre =>
          have e := (List.cons.inj split).2
          cases pre with
          | nil => cases k <;> simp [readingBar] at e
          | cons b rest =>
              have eb := (List.cons.inj e).1
              have et := (List.cons.inj e).2
              obtain ⟨before,after⟩ := ih et
              refine ⟨?_,after⟩
              rcases before with hr | ⟨front,kind,degree,hr⟩
              · subst rest
                exact .inr ⟨[a],k,d,by simp only [List.cons_append,List.nil_append]; rw [←eb]⟩
              · exact .inr ⟨a::b::front,kind,degree,by rw [hr]; rfl⟩

private theorem keyed_atom_split (s : Nat → Label)
    (same : (pre++(.atom n::post)).map (Letter.outerImageKey s)=ys.map (Letter.outerImageKey s)) :
    ∃ before m after, ys=before++(.atom m::after) ∧ pre.length=before.length ∧
      post.length=after.length ∧ s n=s m ∧
      pre.map (Letter.outerImageKey s)=before.map (Letter.outerImageKey s) ∧
      post.map (Letter.outerImageKey s)=after.map (Letter.outerImageKey s) := by
  induction pre generalizing ys with
  | nil =>
      cases ys with
      | nil => simp at same
      | cons y rest =>
          have e := List.cons.inj same
          cases y with
          | atom m =>
              refine ⟨[],m,rest,rfl,rfl,?_,Sum.inl.inj e.1,rfl,e.2⟩
              simpa only [List.length_map] using congrArg List.length e.2
          | over d => cases e.1
          | under d => cases e.1
  | cons a pre ih =>
      cases ys with
      | nil => simp at same
      | cons b rest =>
          have e := List.cons.inj same
          obtain ⟨before,m,after,hr,hb,ha,hi,hbk,hak⟩ := ih e.2
          exact ⟨b::before,m,after,by rw [hr]; rfl,by simpa using hb,ha,hi,
            by simp only [List.map_cons]; rw [e.1,hbk],hak⟩

private theorem bar_key (s : Nat → Label) (k : Bool) (d : Label) :
    Letter.outerImageKey s (readingBar k d)=.inr k := by cases k <;> rfl

private theorem paired_shape (s : Nat → Label)
    (left : AtomBarWord (lp++(.atom n::la))) (right : AtomBarWord (rp++(.atom m::ra)))
    (pl : lp.length=rp.length) (al : la.length=ra.length)
    (pk : lp.map (Letter.outerImageKey s)=rp.map (Letter.outerImageKey s))
    (ak : la.map (Letter.outerImageKey s)=ra.map (Letter.outerImageKey s)) :
    Nonempty (PairedDirectedCellShape lp rp la ra) := by
  obtain ⟨lpNear,laFar⟩ := left.neighbors rfl
  obtain ⟨rpNear,raFar⟩ := right.neighbors rfl
  rcases lpNear with rfl | ⟨lb,lk,ld,rfl⟩
  · have hr : rp=[] := List.length_eq_zero_iff.mp (by simpa using pl.symm)
    subst rp
    rcases laFar with rfl | ⟨lk,ld,lt,rfl⟩
    · have hr : ra=[] := List.length_eq_zero_iff.mp (by simpa using al.symm)
      subst ra
      exact ⟨.singleton⟩
    · rcases raFar with hr | ⟨rk,rd,rt,rfl⟩
      · simp [hr] at al
      · have eq := (List.cons.inj ak).1
        simp only [bar_key] at eq
        have kinds := Sum.inr.inj eq
        subst rk
        exact ⟨.first lk ld rd lt rt⟩
  · rcases rpNear with hr | ⟨rb,rk,rd,rfl⟩
    · simp [hr] at pl
    · have eq := congrArg List.getLast? pk
      simp only [List.map_append,List.map_singleton,List.getLast?_append,bar_key] at eq
      have kinds : lk=rk := by simpa using eq
      subst rk
      rcases laFar with rfl | ⟨lf,lfd,lt,rfl⟩
      · have hr : ra=[] := List.length_eq_zero_iff.mp (by simpa using al.symm)
        subst ra
        exact ⟨.last lk ld rd lb rb⟩
      · rcases raFar with hr | ⟨rf,rfd,rt,rfl⟩
        · simp [hr] at al
        · have eq := (List.cons.inj ak).1
          simp only [bar_key] at eq
          have kinds := Sum.inr.inj eq
          subst rf
          exact ⟨.interior lk lf ld rd lfd rfd lb rb lt rt⟩

theorem directed_atom_cell (left : labelLeft.Alternating) (right : labelRight.Alternating)
    (same : (labelLeft.readLetters forward).map (Letter.outerImageKey s)=
      (labelRight.readLetters forward).map (Letter.outerImageKey s))
    (split : labelLeft.readLetters forward=pre++(.atom n::post)) :
    Nonempty (PairedDirectedAtomCell s (labelLeft.readLetters forward)
      (labelRight.readLetters forward) pre n post) := by
  have keys := same
  rw [split] at keys
  obtain ⟨before,m,after,hr,hb,ha,hi,hbk,hak⟩ := keyed_atom_split s keys
  have leftWord := left.readAtomBarWord forward
  have rightWord := right.readAtomBarWord forward
  rw [split] at leftWord
  rw [hr] at rightWord
  obtain ⟨shape⟩ := paired_shape s leftWord rightWord hb ha hbk hak
  refine ⟨⟨m,before,after,split,hr,hb,ha,?_,?_,hi,hbk,hak,shape⟩⟩
  · rw [hr,hb]
    simp
  · rw [hr,hb]
    simp

theorem PairedDirectedAtomCell.writing_windows
    (cell : PairedDirectedAtomCell s (left.readLetters forward)
      (right.readLetters forward) pre n post) :
    left.letters=(if forward then pre++(.atom n::post)
      else post.reverse++[.atom n]++pre.reverse) ∧
    right.letters=(if forward then cell.rightBefore++(.atom cell.rightAtom::cell.rightAfter)
      else cell.rightAfter.reverse++[.atom cell.rightAtom]++cell.rightBefore.reverse) := by
  cases forward with
  | true => exact ⟨cell.leftSplit,cell.rightSplit⟩
  | false =>
      have l := congrArg List.reverse cell.leftSplit
      have r := congrArg List.reverse cell.rightSplit
      simpa [Label.readLetters,List.reverse_append,List.reverse_cons,List.append_assoc] using And.intro l r

end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Marked
open Labelled

theorem RelativeOldHistory.directed_outer_atom_cells
    (leftOld : RelativeOldHistory F ps (mark F source.erase) leftMarked)
    (rightOld : RelativeOldHistory F qs (mark F source.erase) rightMarked)
    (leftLabels : Labelled.History ps source leftTarget)
    (rightLabels : Labelled.History qs source rightTarget)
    (leftLocal : Labelled.History ps (initLabels source.erase) leftBasis)
    (rightLocal : Labelled.History qs (initLabels source.erase) rightBasis)
    (selected : ∀ p∈F,source.degreeAt p=some alpha)
    (sourceSafe : source.OuterBarsSafe (fun d=>d≠alpha))
    (leftAt : leftTarget.subterm p=some leftNode)
    (rightAt : rightTarget.subterm q=some rightNode)
    (leftLocalAt : leftBasis.subterm p=some leftLocalNode)
    (rightLocalAt : rightBasis.subterm q=some rightLocalNode)
    (sameLabel : leftNode.label=rightNode.label) (forward : Bool) :
    Nonempty (DirectedOuterAtomCells (initialRelabelling source 0)
      leftLocalNode.label rightLocalNode.label forward) := by
  have lAlt := leftLocal.generated_label_alternating (init_is_INIT _)
    (LTerm.label_mem_of_subterm leftLocalAt)
  have rAlt := rightLocal.generated_label_alternating (init_is_INIT _)
    (LTerm.label_mem_of_subterm rightLocalAt)
  have writing := leftOld.local_outer_image_alignment rightOld leftLabels rightLabels
    leftLocal rightLocal selected sourceSafe leftAt rightAt leftLocalAt rightLocalAt sameLabel
  have reading : (leftLocalNode.label.readLetters forward).map
      (Letter.outerImageKey (initialRelabelling source 0))=
      (rightLocalNode.label.readLetters forward).map
        (Letter.outerImageKey (initialRelabelling source 0)) := by
    cases forward
    · simpa [Label.readLetters,List.map_reverse] using congrArg List.reverse writing
    · exact writing
  refine ⟨⟨lAlt,rAlt,reading,?_,?_,?_⟩⟩
  · simpa only [List.length_map] using congrArg List.length reading
  · intro pre n post split
    exact directed_atom_cell lAlt rAlt reading split
  · intro pre n post split
    exact directed_atom_cell rAlt lAlt reading.symm split

end Lamping.Lambda.Marked
