import Lamping.Lamping.MarkerNoCopy
namespace Lamping.AG.Marker
open Graph Lambda
namespace TaggedLevel
 def word (target : Origin) : List Bool → TaggedLevel → TaggedLevel
  | [],a => a
  | false::xs,a => .o target (word target xs a)
  | true::xs,a => .star target (word target xs a)
 /-- Replace the selected unary marker by an arbitrary (possibly empty) word.
Other marker constructors, their children and physical path remain explicit. -/
 def rewrite (target : Origin) (xs : List Bool) : TaggedLevel → TaggedLevel
  | .empty => .empty
  | .o tag a => if tag=target then word target xs (rewrite target xs a) else .o tag (rewrite target xs a)
  | .star tag a => if tag=target then word target xs (rewrite target xs a) else .star tag (rewrite target xs a)
  | .pair tag a b => .pair tag (rewrite target xs a) (rewrite target xs b)
 def HasUnary (target : Origin) : TaggedLevel → Prop
  | .empty => False
  | .o tag a | .star tag a => tag=target ∨ HasUnary target a
  | .pair _ a b => HasUnary target a ∨ HasUnary target b
 theorem HasUnary.mem {target : Origin} {a : TaggedLevel} (h : HasUnary target a) : target∈a.origins := by
  induction a with
  | empty => exact False.elim h
  | o tag a ih | star tag a ih =>
    rcases h with same | child
    · simp [origins,same]
    · exact List.mem_cons_of_mem tag (ih child)
  | pair tag a b ia ib =>
    rcases h with left | right
    · simp only [origins,List.mem_cons,List.mem_append]
      exact Or.inr (Or.inl (ia left))
    · simp only [origins,List.mem_cons,List.mem_append]
      exact Or.inr (Or.inr (ib right))
end TaggedLevel
namespace TaggedContext
 def rewrite (target : Origin) (xs : List Bool) (a : TaggedContext) : TaggedContext :=
  ⟨fun k => TaggedLevel.rewrite target xs (a.get k),by
    obtain ⟨n,hn⟩ := a.finite
    exact ⟨n,by intro k hk; simp [hn k hk,TaggedLevel.rewrite]⟩⟩
 @[simp] theorem rewrite_cons (target : Origin) (xs : List Bool) (a : TaggedContext) (x : TaggedLevel) :
    rewrite target xs (a.cons x)=(rewrite target xs a).cons (TaggedLevel.rewrite target xs x) := by
  ext k
  cases k <;> rfl
 @[simp] theorem rewrite_replace (target : Origin) (xs : List Bool) (a b : TaggedContext) (i : Nat) :
    rewrite target xs (a.replace i b)=(rewrite target xs a).replace i (rewrite target xs b) := by
  ext k
  by_cases low : k<i <;> simp [rewrite,replace,low]
 def HasUnaryOrigin (target : Origin) (a : TaggedContext) : Prop := ∃ k,TaggedLevel.HasUnary target (a.get k)
 theorem HasUnaryOrigin.hasOrigin {target : Origin} {a : TaggedContext} (h : HasUnaryOrigin target a) :
    HasOrigin target a := by
  obtain ⟨k,hk⟩ := h
  exact ⟨k,hk.mem⟩
end TaggedContext

/-- Replay commutes with a direct passage when its constructor is not the
selected old marker. The premise is discharged by actual origins below. -/
theorem TaggedPassage.rewrite {writer i kind p q a b} (h : TaggedPassage writer i kind p q a b)
    (target : Origin) (xs : List Bool) (different : WriteKind kind p q → writer≠target) :
    TaggedPassage writer i kind p q (TaggedContext.rewrite target xs a) (TaggedContext.rewrite target xs b) := by
  cases h with
  | fanO s c x =>
    have neq := different True.intro
    simpa only [TaggedContext.rewrite_replace,TaggedContext.rewrite_cons,TaggedLevel.rewrite,if_neg neq] using
      TaggedPassage.fanO (origin:=writer) (TaggedContext.rewrite target xs s) (TaggedContext.rewrite target xs c)
        (TaggedLevel.rewrite target xs x)
  | fanStar s c x =>
    have neq := different True.intro
    simpa only [TaggedContext.rewrite_replace,TaggedContext.rewrite_cons,TaggedLevel.rewrite,if_neg neq] using
      TaggedPassage.fanStar (origin:=writer) (TaggedContext.rewrite target xs s) (TaggedContext.rewrite target xs c)
        (TaggedLevel.rewrite target xs x)
  | cro s c =>
    simpa only [TaggedContext.rewrite_replace,TaggedContext.rewrite_cons,TaggedLevel.rewrite] using
      TaggedPassage.cro (origin:=writer) (TaggedContext.rewrite target xs s) (TaggedContext.rewrite target xs c)
  | bra s c x y =>
    simpa only [TaggedContext.rewrite_replace,TaggedContext.rewrite_cons,TaggedLevel.rewrite] using
      TaggedPassage.bra (origin:=writer) (TaggedContext.rewrite target xs s) (TaggedContext.rewrite target xs c)
        (TaggedLevel.rewrite target xs x) (TaggedLevel.rewrite target xs y)
  | appFun => exact .appFun _
  | appArg => exact .appArg _
  | lamBody => exact .lamBody _

/-- A final surviving old marker cannot be the constructor consumed by an
inverse step: no-copy rules out a second simultaneous occurrence. -/
theorem TaggedTraversal.rewrite_old {event i kind p q a b} (h : TaggedTraversal event i kind p q a b)
    (level : Nat) (address : List Bool) (xs : List Bool) (unique : UniqueOrigins a)
    (survives : TaggedContext.HasOrigin (.input level address) b) :
    TaggedTraversal event i kind p q
      (TaggedContext.rewrite (.input level address) xs a) (TaggedContext.rewrite (.input level address) xs b) := by
  cases h with
  | direct step =>
    apply TaggedTraversal.direct
    exact step.rewrite _ xs (by intro writes impossible; cases impossible)
  | inverse writer step =>
    apply TaggedTraversal.inverse writer
    apply step.rewrite _ xs
    intro writes same
    subst writer
    exact step.no_surviving_own_origin writes unique survives

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

 theorem TaggedTurn.old_present {event e f a b} (h : TaggedTurn g event e f a b)
    (level : Nat) (address : List Bool) (present : TaggedContext.HasOrigin (.input level address) b) :
    TaggedContext.HasOrigin (.input level address) a := by
  cases h with
  | node n p q rule =>
    rcases rule.origin_membership _ present with impossible | old
    · cases impossible
    · exact old
  | transparent => exact present

 theorem TaggedLabelling.old_present {event es a b} (h : TaggedLabelling g event es a b)
    (level : Nat) (address : List Bool) (present : TaggedContext.HasOrigin (.input level address) b) :
    TaggedContext.HasOrigin (.input level address) a := by
  induction h with
  | single => exact present
  | cons turn tail ih => exact turn.old_present level address (ih present)

 theorem TaggedTurn.rewrite_old {event e f a b} (h : TaggedTurn g event e f a b)
    (level : Nat) (address : List Bool) (xs : List Bool) (unique : UniqueOrigins a)
    (survives : TaggedContext.HasOrigin (.input level address) b) :
    TaggedTurn g event e f (TaggedContext.rewrite (.input level address) xs a)
      (TaggedContext.rewrite (.input level address) xs b) := by
  cases h with
  | node n p q rule => exact .node n p q (rule.rewrite_old level address xs unique survives)
  | transparent w d a => exact .transparent w d _

 theorem TaggedLabelling.rewrite_old {event es a b} (h : TaggedLabelling g event es a b)
    (level : Nat) (address : List Bool) (xs : List Bool)
    (unique : UniqueOrigins a) (causal : OriginsBefore event a)
    (survives : TaggedContext.HasOrigin (.input level address) b) :
    TaggedLabelling g event es (TaggedContext.rewrite (.input level address) xs a)
      (TaggedContext.rewrite (.input level address) xs b) := by
  induction h with
  | single event e a => exact .single event e _
  | cons turn tail ih =>
    have middleSurvives := tail.old_present level address survives
    exact .cons (turn.rewrite_old level address xs unique middleSurvives)
      (ih (turn.no_copy unique causal.fresh) (turn.originsBefore causal) survives)

/-- A true actual path admits replay after replacing its unique surviving old
unary marker by any O/Star word, including the empty word. This preserves the
physical path and changes the actual input/output contexts by explicit maps. -/
theorem old_marker_replay {es a b} (h : Labelling g es a b) :
    ∃ output, TaggedLabelling g 0 es (TaggedContext.initial a) output ∧ output.erase=b ∧
      UniqueOrigins output ∧
      ∀ level address xs, TaggedContext.HasUnaryOrigin (.input level address) output →
        Labelling g es (TaggedContext.rewrite (.input level address) xs (TaggedContext.initial a)).erase
          (TaggedContext.rewrite (.input level address) xs output).erase := by
  obtain ⟨output,tagged,erased,unique,writers⟩ := actual_path_no_copy h
  refine ⟨output,tagged,erased,unique,?_⟩
  intro level address xs present
  exact (tagged.rewrite_old level address xs (TaggedContext.initial_unique a)
    (TaggedContext.initial_originsBefore a) present.hasOrigin).erase
end
end Lamping.AG.Marker
