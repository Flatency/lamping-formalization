import Lamping.Lamping.MarkerReplay
import Lamping.Lamping.ExpandedIndependence
namespace Lamping.AG.Marker
open Graph Lambda

/-- A subtree consisting entirely of input constructors may vary freely with
input. A written constructor never belongs to this class. -/
inductive OldLevel : TaggedLevel → Prop
  | empty : OldLevel .empty
  | o (level address) {a} : OldLevel a → OldLevel (.o (.input level address) a)
  | star (level address) {a} : OldLevel a → OldLevel (.star (.input level address) a)
  | pair (level address) {a b} : OldLevel a → OldLevel b → OldLevel (.pair (.input level address) a b)

theorem OldLevel.initial (level address) (a : Level) : OldLevel (TaggedLevel.initial level address a) := by
  induction a generalizing address with
  | empty => exact .empty
  | o a ih => exact .o _ _ (ih _)
  | star a ih => exact .star _ _ (ih _)
  | pair a b ia ib => exact .pair _ _ (ia _) (ib _)

theorem OldLevel.no_written {a} (h : OldLevel a) (event : Nat) : .written event∉a.origins := by
  induction h <;> simp_all [TaggedLevel.origins]

/-- Input origins can vary; an actual writer ordinal must agree. -/
inductive SameSource : Origin → Origin → Prop
  | input (level address otherLevel otherAddress) :
      SameSource (.input level address) (.input otherLevel otherAddress)
  | written (event) : SameSource (.written event) (.written event)

/-- Written constructors have the same shape and tree position. Entire old
subtrees may vary, so this does not require equal input contexts. -/
inductive RigidLevel : TaggedLevel → TaggedLevel → Prop
  | old {a b} : OldLevel a → OldLevel b → RigidLevel a b
  | o {tag other a b} : SameSource tag other → RigidLevel a b → RigidLevel (.o tag a) (.o other b)
  | star {tag other a b} : SameSource tag other → RigidLevel a b → RigidLevel (.star tag a) (.star other b)
  | pair {tag other a b c d} : SameSource tag other → RigidLevel a c → RigidLevel b d →
      RigidLevel (.pair tag a b) (.pair other c d)

namespace RigidLevel
 theorem o_child {tag other a b} (h : RigidLevel (.o tag a) (.o other b)) : RigidLevel a b := by
  cases h with
  | old ha hb => cases ha; cases hb; exact .old (by assumption) (by assumption)
  | o _ child => exact child
 theorem star_child {tag other a b} (h : RigidLevel (.star tag a) (.star other b)) : RigidLevel a b := by
  cases h with
  | old ha hb => cases ha; cases hb; exact .old (by assumption) (by assumption)
  | star _ child => exact child
 theorem pair_children {tag other a b c d} (h : RigidLevel (.pair tag a b) (.pair other c d)) :
     RigidLevel a c ∧ RigidLevel b d := by
  cases h with
  | old ha hb => cases ha; cases hb; exact ⟨.old (by assumption) (by assumption),.old (by assumption) (by assumption)⟩
  | pair _ left right => exact ⟨left,right⟩
 theorem written_o {event a b} (h : RigidLevel (.o (.written event) a) b) :
     ∃ child,b=.o (.written event) child ∧ RigidLevel a child := by
  cases h with
  | old impossible => cases impossible
  | o source child => cases source; exact ⟨_,rfl,child⟩
 theorem written_star {event a b} (h : RigidLevel (.star (.written event) a) b) :
     ∃ child,b=.star (.written event) child ∧ RigidLevel a child := by
  cases h with
  | old impossible => cases impossible
  | star source child => cases source; exact ⟨_,rfl,child⟩
 theorem written_pair {event a b c} (h : RigidLevel (.pair (.written event) a b) c) :
     ∃ left right,c=.pair (.written event) left right ∧ RigidLevel a left ∧ RigidLevel b right := by
  cases h with
  | old impossible => cases impossible
  | pair source left right => cases source; exact ⟨_,_,rfl,left,right⟩
end RigidLevel

def RigidContext (a b : TaggedContext) : Prop := ∀ k,RigidLevel (a.get k) (b.get k)
namespace RigidContext
 theorem initial (a b : Context) : RigidContext (TaggedContext.initial a) (TaggedContext.initial b) :=
  fun k => .old (OldLevel.initial k [] _) (OldLevel.initial k [] _)
 theorem cons {a b x y} (h : RigidContext a b) (head : RigidLevel x y) :
     RigidContext (a.cons x) (b.cons y) := by
  intro k
  cases k with | zero => exact head | succ k => exact h k
 theorem replace {a b c d} (shell : RigidContext a b) (tail : RigidContext c d) (i : Nat) :
     RigidContext (a.replace i c) (b.replace i d) := by
  intro k
  by_cases low : k<i <;> simp only [TaggedContext.replace,low,ite_true,ite_false]
  · exact shell k
  · exact tail (k-i)
 theorem tail {a b} (h : RigidContext a b) (i : Nat) : RigidContext (a.tail i) (b.tail i) :=
  fun k => h (i+k)
 theorem replace_head {s t a b : TaggedContext} {x y : TaggedLevel} {i : Nat}
     (h : RigidContext (s.replace i (a.cons x)) (t.replace i (b.cons y)))
     (u v : TaggedLevel) (head : RigidLevel u v) :
     RigidContext (s.replace i (a.cons u)) (t.replace i (b.cons v)) := by
  intro k
  by_cases low : k<i
  · simpa only [TaggedContext.replace,if_pos low] using h k
  · by_cases eq : k=i
    · subst k; simpa [TaggedContext.replace,TaggedContext.cons] using head
    · have hd : k-i=(k-i-1)+1 := by omega
      have hk := h k
      simp only [TaggedContext.replace,if_neg low] at hk ⊢
      rw [hd] at hk ⊢
      exact hk
 theorem head {s t a b : TaggedContext} {x y : TaggedLevel} {i : Nat}
     (h : RigidContext (s.replace i (a.cons x)) (t.replace i (b.cons y))) : RigidLevel x y := by
  simpa [TaggedContext.replace,TaggedContext.cons] using h i
 theorem tail_of_replace {s t a b : TaggedContext} {i : Nat}
     (h : RigidContext (s.replace i a) (t.replace i b)) : RigidContext a b := by
  intro k
  simpa [TaggedContext.replace,show ¬i+k<i by omega] using h (i+k)
 theorem reshell {s t a b c d : TaggedContext} {i : Nat}
     (h : RigidContext (s.replace i a) (t.replace i b)) (tail : RigidContext c d) :
     RigidContext (s.replace i c) (t.replace i d) := by
  intro k
  by_cases low : k<i
  · simpa only [TaggedContext.replace,if_pos low] using h k
  · simpa only [TaggedContext.replace,if_neg low] using tail (k-i)
 theorem uncons {a b : TaggedContext} {x y : TaggedLevel} (h : RigidContext (a.cons x) (b.cons y)) :
     RigidLevel x y ∧ RigidContext a b := ⟨h 0,fun k => h (k+1)⟩
end RigidContext

/-- Both actual runs make the same direct local passage. Different old input
subtrees remain allowed; constructors emitted at this turn have one writer. -/
theorem TaggedPassage.rigid_forward {writer other i kind p q a b c d}
    (h : TaggedPassage writer i kind p q a b) (k : TaggedPassage other i kind p q c d)
    (source : SameSource writer other) (rigid : RigidContext a c) : RigidContext b d := by
  cases h <;> cases k
  case fanO.fanO => exact rigid.replace_head _ _ (.o source rigid.head)
  case fanStar.fanStar => exact rigid.replace_head _ _ (.star source rigid.head)
  case cro.cro => exact rigid.reshell (rigid.tail_of_replace.cons (.old .empty .empty))
  case bra.bra =>
    have heads := rigid.tail_of_replace.uncons
    have next := heads.2.uncons
    exact rigid.reshell (next.2.cons (.pair source next.1 heads.1))
  case appFun.appFun | appArg.appArg | lamBody.lamBody => exact rigid

/-- Inverse passages only expose already corresponding children; the two
consumed origins need not be equal or newly written at this inverse turn. -/
theorem TaggedPassage.rigid_backward {writer other i kind p q a b c d}
    (h : TaggedPassage writer i kind p q a b) (k : TaggedPassage other i kind p q c d)
    (rigid : RigidContext b d) : RigidContext a c := by
  cases h <;> cases k
  case fanO.fanO => exact rigid.replace_head _ _ rigid.head.o_child
  case fanStar.fanStar => exact rigid.replace_head _ _ rigid.head.star_child
  case cro.cro => exact rigid.reshell rigid.tail_of_replace.uncons.2
  case bra.bra =>
    have heads := rigid.tail_of_replace.uncons
    have children := heads.1.pair_children
    exact rigid.reshell ((heads.2.cons children.1).cons children.2)
  case appFun.appFun | appArg.appArg | lamBody.lamBody => exact rigid
 theorem TaggedTraversal.rigid {event i kind p q a b c d}
     (h : TaggedTraversal event i kind p q a b) (k : TaggedTraversal event i kind p q c d)
     (input : RigidContext a c) : RigidContext b d := by
  cases h with
  | direct hp =>
    cases k with
    | direct kp => exact hp.rigid_forward kp (.written event) input
    | inverse other kp => cases hp <;> cases kp
  | inverse writer hp =>
    cases k with
    | direct kp => cases hp <;> cases kp
    | inverse other kp => exact hp.rigid_backward kp input

inductive MarkerShape where
  | o | star | pair
  deriving DecidableEq, Repr

/-- Literal tree position, with false for a unary child or pair's left child. -/
def TaggedLevel.constructorAt : List Bool → TaggedLevel → Option (Origin × MarkerShape)
  | [],.empty => none
  | [],.o tag _ => some (tag,.o)
  | [],.star tag _ => some (tag,.star)
  | [],.pair tag _ _ => some (tag,.pair)
  | _::_,.empty => none
  | false::xs,.o _ child | false::xs,.star _ child => child.constructorAt xs
  | true::_,.o _ _ | true::_,.star _ _ => none
  | false::xs,.pair _ left _ => left.constructorAt xs
  | true::xs,.pair _ _ right => right.constructorAt xs

 theorem OldLevel.no_written_at {a} (h : OldLevel a) (address : List Bool) (event : Nat) (shape : MarkerShape) :
     a.constructorAt address≠some (.written event,shape) := by
  induction h generalizing address with
  | empty => cases address <;> simp [TaggedLevel.constructorAt]
  | o level addr ha ih | star level addr ha ih =>
    cases address with
    | nil => simp [TaggedLevel.constructorAt]
    | cons bit rest => cases bit <;> simp [TaggedLevel.constructorAt,ih]
  | pair level addr ha hb ia ib =>
    cases address with
    | nil => simp [TaggedLevel.constructorAt]
    | cons bit rest => cases bit <;> simp [TaggedLevel.constructorAt,ia,ib]

/-- The writer and constructor at a literal final position are rigid across
arbitrary valid input labels; this is stronger than mere origin membership. -/
theorem RigidLevel.written_at {a b} (h : RigidLevel a b) (address : List Bool) (event : Nat) (shape : MarkerShape)
    (present : a.constructorAt address=some (.written event,shape)) :
    b.constructorAt address=some (.written event,shape) := by
  induction h generalizing address with
  | old ha hb => exact False.elim (ha.no_written_at address event shape present)
  | o source child ih | star source child ih =>
    cases address with
    | nil => cases source with
      | input => simp [TaggedLevel.constructorAt] at present
      | written => exact present
    | cons bit rest =>
      cases bit with
      | false => exact ih rest present
      | true => cases present
  | pair source left right ia ib =>
    cases address with
    | nil => cases source with
      | input => simp [TaggedLevel.constructorAt] at present
      | written => exact present
    | cons bit rest => cases bit with
      | false => exact ia rest present
      | true => exact ib rest present

def levelMarkerAt : List Bool → Level → Option MarkerShape
  | [],.empty => none
  | [],.o _ => some .o
  | [],.star _ => some .star
  | [],.pair _ _ => some .pair
  | _::_,.empty => none
  | false::xs,.o child | false::xs,.star child => levelMarkerAt xs child
  | true::_,.o _ | true::_,.star _ => none
  | false::xs,.pair left _ => levelMarkerAt xs left
  | true::xs,.pair _ right => levelMarkerAt xs right

 theorem TaggedLevel.markerAt_erase (a : TaggedLevel) (address : List Bool) :
     Option.map Prod.snd (a.constructorAt address)=levelMarkerAt address a.erase := by
  induction a generalizing address with
  | empty => cases address <;> simp [TaggedLevel.constructorAt,TaggedLevel.erase,levelMarkerAt]
  | o tag a ih | star tag a ih =>
    cases address with
    | nil => rfl
    | cons bit rest => cases bit with
      | false => exact ih rest
      | true => rfl
  | pair tag a b ia ib =>
    cases address with
    | nil => rfl
    | cons bit rest => cases bit with
      | false => exact ia rest
      | true => exact ib rest

section Paths
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
 theorem TaggedTurn.rigid {event e f a b c d} (h : TaggedTurn g event e f a b)
     (k : TaggedTurn g event e f c d) (input : RigidContext a c) : RigidContext b d := by
  cases h with
  | node n p q rule =>
    cases k with
    | node n p q other => exact rule.rigid other input
  | transparent => cases k; exact input
 theorem TaggedLabelling.rigid {event es a b c d} (h : TaggedLabelling g event es a b)
     (k : TaggedLabelling g event es c d) (input : RigidContext a c) : RigidContext b d := by
  induction h generalizing c d with
  | single => cases k; exact input
  | cons turn tail ih =>
    cases k with
    | cons other rest => exact ih rest (turn.rigid other input)

/-- Every pair of actual labellings of one physical path has a genuine tagged
lift whose written constructors agree at each final level and tree position. -/
theorem actual_written_rigidity {es a b c d} (h : Labelling g es a b) (k : Labelling g es c d) :
    ∃ first second, TaggedLabelling g 0 es (TaggedContext.initial a) first ∧ first.erase=b ∧
      TaggedLabelling g 0 es (TaggedContext.initial c) second ∧ second.erase=d ∧ RigidContext first second := by
  obtain ⟨first,ht,hb⟩ := initial_lift g h
  obtain ⟨second,kt,kd⟩ := initial_lift g k
  exact ⟨first,second,ht,hb,kt,kd,ht.rigid kt (RigidContext.initial a c)⟩
/-- A marker actually written during one run has its constructor fixed at the
same final position in every other valid labelling, even with a different input. -/
theorem written_marker_fixed {es a output} (h : TaggedLabelling g 0 es (TaggedContext.initial a) output)
    (level : Nat) (address : List Bool) (event : Nat) (shape : MarkerShape)
    (written : (output.get level).constructorAt address=some (.written event,shape))
    {c d} (other : Labelling g es c d) : levelMarkerAt address (d.get level)=some shape := by
  obtain ⟨second,tagged,erased⟩ := initial_lift g other
  have rigid := h.rigid tagged (RigidContext.initial a c)
  have same := (rigid level).written_at address event shape written
  have visible := congrArg (Option.map Prod.snd) same
  rw [TaggedLevel.markerAt_erase] at visible
  change levelMarkerAt address ((second.erase).get level)=some shape at visible
  simpa only [erased] using visible
/-- A genuinely variable output tail contains no constructor emitted by the
path. The quantified labels are supplied by independence, not postulated as
an invariant field of a graph. -/
theorem free_tail_no_written {es a output} (h : TaggedLabelling g 0 es (TaggedContext.initial a) output)
    (width : Nat)
    (varies : ∀ tail : Context, ∃ input, Labelling g es input (output.erase.replace width tail))
    (level : Nat) (high : width≤level) (address : List Bool) (event : Nat) (shape : MarkerShape) :
    (output.get level).constructorAt address≠some (.written event,shape) := by
  intro written
  obtain ⟨input,labels⟩ := varies Context.empty
  have fixed := written_marker_fixed h level address event shape written labels
  have emptyLevel : (output.erase.replace width Context.empty).get level=Level.empty := by
    simp [Context.replace,show ¬level<width by omega,Context.empty]
  rw [emptyLevel] at fixed
  cases address <;> simp [levelMarkerAt] at fixed
/-- AG3.5.6(iii), with the actual terminal width and source strictness supplied
by ordinary independence. Fan and bracket constructors are both covered. -/
theorem no_written_terminal_tail {root : B} (indep : Independence g root)
    {es a output} (h : TaggedLabelling g 0 es (TaggedContext.initial a) output)
    (e f : Endpoint g) (sr tr : ProperRole) (m n : Nat)
    (start : es.head?=some e) (finish : es.getLast?=some (g.wire f))
    (source : AtProperRole g root e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole g root f tr n) (incoming : tr.incoming) (fw : Forward g es) :
    ∃ width, m≤width ∧ (sr=.appArg → m<width) ∧
      ∀ level, tr.terminalWidth n≤level → ∀ address event shape,
        (output.get level).constructorAt address≠some (.written event,shape) := by
  have labels : Labelling g es a output.erase := by simpa using h.erase
  obtain ⟨_,width,lower,strict,_,sync⟩ := indep.forward_tail es e f sr tr m n a output.erase
    start finish source outgoing target incoming fw labels
  refine ⟨width,lower,strict,?_⟩
  intro level high address event shape
  apply free_tail_no_written h (tr.terminalWidth n) ?_ level high address event shape
  intro tail
  exact ⟨a.replace width tail,sync tail⟩
end Paths
end Lamping.AG.Marker











