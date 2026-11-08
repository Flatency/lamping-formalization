import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG.Marker
open Graph Lambda

/-- An old marker has a precise input level/tree address; a new constructor
has the unique ordinal of the actual traversed control turn. -/
inductive Origin where
  | input (level : Nat) (address : List Bool)
  | written (turn : Nat)
  deriving DecidableEq, Repr

inductive TaggedLevel where
  | empty
  | o (origin : Origin) (child : TaggedLevel)
  | star (origin : Origin) (child : TaggedLevel)
  | pair (origin : Origin) (left right : TaggedLevel)
  deriving DecidableEq, Repr
namespace TaggedLevel
 def erase : TaggedLevel → Level
  | .empty => .empty
  | .o _ a => .o a.erase
  | .star _ a => .star a.erase
  | .pair _ a b => .pair a.erase b.erase
 def origins : TaggedLevel → List Origin
  | .empty => []
  | .o tag a | .star tag a => tag::a.origins
  | .pair tag a b => tag::(a.origins++b.origins)
 def initial (level : Nat) (address : List Bool) : Level → TaggedLevel
  | .empty => .empty
  | .o a => .o (.input level address) (initial level (address++[false]) a)
  | .star a => .star (.input level address) (initial level (address++[false]) a)
  | .pair a b => .pair (.input level address)
      (initial level (address++[false]) a) (initial level (address++[true]) b)
 @[simp] theorem initial_erase (level : Nat) (address : List Bool) (a : Level) :
    (initial level address a).erase=a := by
  induction a generalizing address <;> simp_all [initial,erase]
 theorem initial_no_written (level : Nat) (address : List Bool) (a : Level) (event : Nat) :
    Origin.written event ∉ (initial level address a).origins := by
  induction a generalizing address <;> simp_all [initial,origins]
end TaggedLevel

/-- Tagged contexts retain the same finite-support convention as Context. -/
structure TaggedContext where
  get : Nat → TaggedLevel
  finite : ∃ n, ∀ k, n≤k → get k=.empty
namespace TaggedContext
 @[ext] theorem ext {a b : TaggedContext} (h : ∀ k, a.get k=b.get k) : a=b := by
  cases a; cases b; congr; funext k; exact h k
 def erase (a : TaggedContext) : Context :=
  ⟨fun k => (a.get k).erase,by obtain ⟨n,hn⟩ := a.finite; exact ⟨n,by intro k hk; simp [hn k hk,TaggedLevel.erase]⟩⟩
 def initial (a : Context) : TaggedContext :=
  ⟨fun k => TaggedLevel.initial k [] (a.get k),by
    obtain ⟨n,hn⟩ := a.finite
    exact ⟨n,by intro k hk; simp [hn k hk,TaggedLevel.initial]⟩⟩
 @[simp] theorem initial_erase (a : Context) : (initial a).erase=a := by
  ext k
  exact TaggedLevel.initial_erase k [] (a.get k)
 def cons (a : TaggedContext) (x : TaggedLevel) : TaggedContext :=
  ⟨fun k => match k with | 0 => x | n+1 => a.get n, by
    obtain ⟨n,hn⟩ := a.finite
    refine ⟨n+1,?_⟩
    intro k hk
    cases k with | zero => omega | succ k => exact hn k (by omega)⟩
 def tail (a : TaggedContext) (n : Nat) : TaggedContext :=
  ⟨fun k => a.get (n+k),by obtain ⟨m,hm⟩ := a.finite; exact ⟨m,by intro k hk; exact hm _ (by omega)⟩⟩
 def replace (a : TaggedContext) (n : Nat) (b : TaggedContext) : TaggedContext :=
  ⟨fun k => if k<n then a.get k else b.get (k-n),by
    obtain ⟨m,hm⟩ := b.finite
    refine ⟨n+m,?_⟩
    intro k hk
    simp only [if_neg (by omega : ¬k<n)]
    exact hm _ (by omega)⟩
 @[simp] theorem erase_cons (a : TaggedContext) (x : TaggedLevel) :
    (a.cons x).erase=a.erase.cons x.erase := by ext k; cases k <;> rfl
 @[simp] theorem erase_tail (a : TaggedContext) (n : Nat) :
    (a.tail n).erase=a.erase.tail n := by ext k; rfl
 @[simp] theorem erase_replace (a b : TaggedContext) (n : Nat) :
    (a.replace n b).erase=a.erase.replace n b.erase := by
  ext k
  by_cases hk : k<n <;> simp [erase,replace,Context.replace,hk]
 theorem replace_tail (a : TaggedContext) (n : Nat) : a.replace n (a.tail n)=a := by
  ext k
  by_cases hk : k<n
  · simp [replace,hk]
  · simp only [replace,if_neg hk,tail]
    congr 1
    omega
 theorem replace_split (a : TaggedContext) (n : Nat) :
    a.replace n ((a.tail (n+1)).cons (a.get n))=a := by
  ext k
  by_cases hk : k<n
  · simp [replace,hk]
  · by_cases he : k=n
    · subst k; simp [replace,cons]
    · have hd : k-n=(k-n-1)+1 := by omega
      change (if k<n then a.get k else ((a.tail (n+1)).cons (a.get n)).get (k-n))=a.get k
      rw [if_neg hk,hd]
      change a.get (n+1+(k-n-1))=a.get k
      congr 1
      omega
 theorem replace_split_two (a : TaggedContext) (n : Nat) :
    a.replace n (((a.tail (n+2)).cons (a.get (n+1))).cons (a.get n))=a := by
  ext k
  by_cases low : k<n
  · simp [replace,low]
  · by_cases first : k=n
    · subst k; simp [replace,cons]
    · by_cases second : k=n+1
      · subst k
        simp [replace,cons,show ¬n+1<n by omega,show n+1-n=1 by omega]
      · have hd : k-n=(k-n-2)+1+1 := by omega
        change (if k<n then a.get k else
          (((a.tail (n+2)).cons (a.get (n+1))).cons (a.get n)).get (k-n))=a.get k
        rw [if_neg low,hd]
        change a.get (n+2+(k-n-2))=a.get k
        congr 1
        omega
end TaggedContext

/-- Direct tagged passages create one named constructor; inverse passages may
consume a constructor with any origin, preserving its child's original tags. -/
inductive TaggedPassage (origin : Origin) (i : Nat) :
    (k : Kind) → Port k → Port k → TaggedContext → TaggedContext → Prop
  | fanO (a b : TaggedContext) (x : TaggedLevel) : TaggedPassage origin i (.op .fan) fanO (.inl ())
      (a.replace i (b.cons x)) (a.replace i (b.cons (.o origin x)))
  | fanStar (a b : TaggedContext) (x : TaggedLevel) : TaggedPassage origin i (.op .fan) fanStar (.inl ())
      (a.replace i (b.cons x)) (a.replace i (b.cons (.star origin x)))
  | cro (a b : TaggedContext) : TaggedPassage origin i (.op .cro) (.inr ()) (.inl ())
      (a.replace i b) (a.replace i (b.cons .empty))
  | bra (a b : TaggedContext) (x y : TaggedLevel) : TaggedPassage origin i (.op .bra) (.inr ()) (.inl ())
      (a.replace i ((b.cons x).cons y)) (a.replace i (b.cons (.pair origin x y)))
  | appFun (a) : TaggedPassage origin i (.op .app) appCtx (.inl ()) a a
  | appArg (a) : TaggedPassage origin i (.op .app) appCtx appArg a a
  | lamBody (a) : TaggedPassage origin i (.op .lam) (.inl ()) lamBody a a

inductive TaggedTraversal (event i : Nat) :
    (k : Kind) → Port k → Port k → TaggedContext → TaggedContext → Prop
  | direct {k p q a b} : TaggedPassage (.written event) i k p q a b →
      TaggedTraversal event i k p q a b
  | inverse {k p q a b} (origin : Origin) : TaggedPassage origin i k p q a b →
      TaggedTraversal event i k q p b a

 theorem TaggedPassage.erase {origin i k p q a b} (h : TaggedPassage origin i k p q a b) :
    Passage i k p q a.erase b.erase := by
  cases h with
  | fanO => simpa only [TaggedContext.erase_replace,TaggedContext.erase_cons,TaggedLevel.erase] using Passage.fanO _ _ _
  | fanStar => simpa only [TaggedContext.erase_replace,TaggedContext.erase_cons,TaggedLevel.erase] using Passage.fanStar _ _ _
  | cro => simpa only [TaggedContext.erase_replace,TaggedContext.erase_cons,TaggedLevel.erase] using Passage.cro _ _
  | bra => simpa only [TaggedContext.erase_replace,TaggedContext.erase_cons,TaggedLevel.erase] using Passage.bra _ _ _ _
  | appFun => exact .appFun _
  | appArg => exact .appArg _
  | lamBody => exact .lamBody _

 theorem TaggedTraversal.erase {event i k p q a b} (h : TaggedTraversal event i k p q a b) :
    Traversal i k p q a.erase b.erase := by
  cases h with
  | direct h => exact .direct h.erase
  | inverse tag h => exact .inverse h.erase

private theorem tagged_o {a : TaggedLevel} {x : Level} (h : a.erase=.o x) :
    ∃ tag child, a=.o tag child := by
  cases a with
  | empty => cases h
  | o tag child => exact ⟨tag,child,rfl⟩
  | star => cases h
  | pair => cases h
private theorem tagged_star {a : TaggedLevel} {x : Level} (h : a.erase=.star x) :
    ∃ tag child, a=.star tag child := by
  cases a with
  | empty => cases h
  | o => cases h
  | star tag child => exact ⟨tag,child,rfl⟩
  | pair => cases h
private theorem tagged_pair {a : TaggedLevel} {x y : Level} (h : a.erase=.pair x y) :
    ∃ tag left right, a=.pair tag left right := by
  cases a with
  | empty => cases h
  | o => cases h
  | star => cases h
  | pair tag left right => exact ⟨tag,left,right,rfl⟩
private theorem tagged_empty {a : TaggedLevel} (h : a.erase=.empty) : a=.empty := by
  cases a <;> first | rfl | cases h

/-- Every real partial control traversal lifts from every correctly erased
input. Direct controls name the current turn; inverse controls consume any
existing origin. The output erases to the *given* actual traversal output. -/
theorem liftTraversal {i k p q a b} (h : Traversal i k p q a b) (event : Nat)
    (input : TaggedContext) (erasure : input.erase=a) :
    ∃ output, TaggedTraversal event i k p q input output ∧ output.erase=b := by
  have possible : ∃ output, TaggedTraversal event i k p q input output := by
    cases h with
    | direct hp =>
      cases hp with
      | fanO s c x =>
        let output := input.replace i ((input.tail (i+1)).cons (.o (.written event) (input.get i)))
        refine ⟨output,?_⟩
        have raw : TaggedTraversal event i (.op .fan) fanO (.inl ())
            (input.replace i ((input.tail (i+1)).cons (input.get i))) output :=
          .direct (.fanO input (input.tail (i+1)) (input.get i))
        simpa only [TaggedContext.replace_split] using raw
      | fanStar s c x =>
        let output := input.replace i ((input.tail (i+1)).cons (.star (.written event) (input.get i)))
        refine ⟨output,?_⟩
        have raw : TaggedTraversal event i (.op .fan) fanStar (.inl ())
            (input.replace i ((input.tail (i+1)).cons (input.get i))) output :=
          .direct (.fanStar input (input.tail (i+1)) (input.get i))
        simpa only [TaggedContext.replace_split] using raw
      | cro s c =>
        let output := input.replace i ((input.tail i).cons .empty)
        refine ⟨output,?_⟩
        have raw : TaggedTraversal event i (.op .cro) (.inr ()) (.inl ())
            (input.replace i (input.tail i)) output := .direct (.cro input (input.tail i))
        simpa only [TaggedContext.replace_tail] using raw
      | bra s c x y =>
        let output := input.replace i ((input.tail (i+2)).cons
          (.pair (.written event) (input.get (i+1)) (input.get i)))
        refine ⟨output,?_⟩
        have raw : TaggedTraversal event i (.op .bra) (.inr ()) (.inl ())
            (input.replace i (((input.tail (i+2)).cons (input.get (i+1))).cons (input.get i))) output :=
          .direct (.bra input (input.tail (i+2)) (input.get (i+1)) (input.get i))
        simpa only [TaggedContext.replace_split_two] using raw
      | appFun => exact ⟨input,.direct (.appFun input)⟩
      | appArg => exact ⟨input,.direct (.appArg input)⟩
      | lamBody => exact ⟨input,.direct (.lamBody input)⟩
    | inverse hp =>
      cases hp with
      | fanO s c x =>
        have head : (input.get i).erase=.o x := by
          have eq := congrArg (fun d : Context => d.get i) erasure
          simpa [TaggedContext.erase,Context.replace,Context.cons] using eq
        obtain ⟨tag,child,hi⟩ := tagged_o head
        let output := input.replace i ((input.tail (i+1)).cons child)
        refine ⟨output,?_⟩
        have raw : TaggedTraversal event i (.op .fan) (.inl ()) fanO
            (input.replace i ((input.tail (i+1)).cons (.o tag child))) output :=
          .inverse tag (.fanO input (input.tail (i+1)) child)
        rw [←hi,TaggedContext.replace_split] at raw
        exact raw
      | fanStar s c x =>
        have head : (input.get i).erase=.star x := by
          have eq := congrArg (fun d : Context => d.get i) erasure
          simpa [TaggedContext.erase,Context.replace,Context.cons] using eq
        obtain ⟨tag,child,hi⟩ := tagged_star head
        let output := input.replace i ((input.tail (i+1)).cons child)
        refine ⟨output,?_⟩
        have raw : TaggedTraversal event i (.op .fan) (.inl ()) fanStar
            (input.replace i ((input.tail (i+1)).cons (.star tag child))) output :=
          .inverse tag (.fanStar input (input.tail (i+1)) child)
        rw [←hi,TaggedContext.replace_split] at raw
        exact raw
      | cro s c =>
        have head : (input.get i).erase=.empty := by
          have eq := congrArg (fun d : Context => d.get i) erasure
          simpa [TaggedContext.erase,Context.replace,Context.cons] using eq
        have hi := tagged_empty head
        let output := input.replace i (input.tail (i+1))
        refine ⟨output,?_⟩
        have raw : TaggedTraversal event i (.op .cro) (.inl ()) (.inr ())
            (input.replace i ((input.tail (i+1)).cons .empty)) output :=
          .inverse (.written event) (.cro input (input.tail (i+1)))
        rw [←hi,TaggedContext.replace_split] at raw
        exact raw
      | bra s c x y =>
        have head : (input.get i).erase=.pair x y := by
          have eq := congrArg (fun d : Context => d.get i) erasure
          simpa [TaggedContext.erase,Context.replace,Context.cons] using eq
        obtain ⟨tag,left,right,hi⟩ := tagged_pair head
        let output := input.replace i (((input.tail (i+1)).cons left).cons right)
        refine ⟨output,?_⟩
        have raw : TaggedTraversal event i (.op .bra) (.inl ()) (.inr ())
            (input.replace i ((input.tail (i+1)).cons (.pair tag left right))) output :=
          .inverse tag (.bra input (input.tail (i+1)) left right)
        rw [←hi,TaggedContext.replace_split] at raw
        exact raw
      | appFun => exact ⟨input,.inverse (.written event) (.appFun input)⟩
      | appArg => exact ⟨input,.inverse (.written event) (.appArg input)⟩
      | lamBody => exact ⟨input,.inverse (.written event) (.lamBody input)⟩
  obtain ⟨output,tagged⟩ := possible
  refine ⟨output,tagged,?_⟩
  have erased := tagged.erase
  rw [erasure] at erased
  exact (h.output_unique erased).symm

section Paths
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

inductive TaggedTurn (event : Nat) : Endpoint g → Endpoint g → TaggedContext → TaggedContext → Prop
  | node (n : N) (p q : Port (g.label n).sort) {a b}
      (rule : TaggedTraversal event (g.label n).index (g.label n).sort p q a b) :
      TaggedTurn event (.inl ⟨n,p⟩) (.inl ⟨n,q⟩) a b
  | transparent (w : W) (d : Bool) (a) :
      TaggedTurn event (.inr (.inr (w,d))) (.inr (.inr (w,!d))) a a

inductive TaggedLabelling : Nat → List (Endpoint g) → TaggedContext → TaggedContext → Prop
  | single (event : Nat) (e a) : TaggedLabelling event [e] a a
  | cons {event e f es a b c} (turn : TaggedTurn g event (g.wire e) f a b)
      (tail : TaggedLabelling (event+1) (f::es) b c) : TaggedLabelling event (e::f::es) a c

 theorem TaggedTurn.erase {event e f a b} (h : TaggedTurn g event e f a b) :
    LabelledTurn g e f a.erase b.erase := by
  cases h with
  | node n p q rule => exact .node n p q rule.erase
  | transparent w d a => exact .transparent w d a.erase

 theorem TaggedLabelling.erase {event es a b} (h : TaggedLabelling g event es a b) :
    Labelling g es a.erase b.erase := by
  induction h with
  | single => exact .single _ _
  | cons turn tail ih => exact .cons turn.erase ih

 theorem liftTurn {e f a b} (h : LabelledTurn g e f a b) (event : Nat)
    (input : TaggedContext) (erasure : input.erase=a) :
    ∃ output, TaggedTurn g event e f input output ∧ output.erase=b := by
  cases h with
  | node n p q rule =>
    obtain ⟨output,tagged,eq⟩ := liftTraversal rule event input erasure
    exact ⟨output,.node n p q tagged,eq⟩
  | transparent w d a => exact ⟨input,.transparent w d input,erasure⟩

/-- Actual repeated turns receive successive event ordinals. Tags are lifted
from the complete supplied physical path, not from a desired provenance field. -/
theorem liftLabelling {es a b} (h : Labelling g es a b) (event : Nat)
    (input : TaggedContext) (erasure : input.erase=a) :
    ∃ output, TaggedLabelling g event es input output ∧ output.erase=b := by
  induction h generalizing event input with
  | single e a => exact ⟨input,.single event e input,erasure⟩
  | cons turn tail ih =>
    obtain ⟨middle,taggedTurn,eq⟩ := liftTurn g turn event input erasure
    obtain ⟨output,taggedTail,last⟩ := ih (event+1) middle eq
    exact ⟨output,.cons taggedTurn taggedTail,last⟩

 theorem initial_lift {es a b} (h : Labelling g es a b) :
    ∃ output, TaggedLabelling g 0 es (TaggedContext.initial a) output ∧ output.erase=b :=
  liftLabelling g h 0 _ (TaggedContext.initial_erase a)
end Paths
end Lamping.AG.Marker




