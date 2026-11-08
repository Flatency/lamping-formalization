import Lamping.Lamping.MarkerRigidity
namespace Lamping.AG.Marker
open Graph Lambda

private def TaggedProperInvariant (kind : Kind) (a b : TaggedContext) : Prop :=
  match kind with | .op .app | .op .lam => a=b | _ => True
private theorem taggedTraversal_proper {event i kind p q a b}
    (h : TaggedTraversal event i kind p q a b) : TaggedProperInvariant kind a b := by
  cases h with
  | direct step => cases step <;> trivial
  | inverse tag step => cases step <;> trivial

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- The only added tagged turns are the two actual beta reversals. Both carry
exactly the same full context across their physical seam. -/
inductive TaggedExpandedTurn (event : Nat) : Endpoint g → Endpoint g → TaggedContext → TaggedContext → Prop
  | ordinary {e f a b} : TaggedTurn g event e f a b → TaggedExpandedTurn event e f a b
  | bindToCtx (r : BetaEdge g) (a) : TaggedExpandedTurn event (.inl ⟨r.lam,r.lamBind⟩) r.ctxEnd a a
  | funToArg (r : BetaEdge g) (a) : TaggedExpandedTurn event r.funEnd r.argEnd a a
inductive TaggedExpandedLabelling : Nat → List (Endpoint g) → TaggedContext → TaggedContext → Prop
  | single (event e a) : TaggedExpandedLabelling event [e] a a
  | cons {event e f es a b c} : TaggedExpandedTurn g event (g.wire e) f a b →
      TaggedExpandedLabelling (event+1) (f::es) b c → TaggedExpandedLabelling event (e::f::es) a c

 theorem TaggedExpandedTurn.erase {event e f a b} (h : TaggedExpandedTurn g event e f a b) :
     ExpandedTurn g e f a.erase b.erase := by
  cases h with
  | ordinary turn => exact .ordinary turn.erase
  | bindToCtx r a => exact .bindToCtx r a.erase
  | funToArg r a => exact .funToArg r a.erase
 theorem TaggedExpandedLabelling.erase {event es a b} (h : TaggedExpandedLabelling g event es a b) :
     ExpandedLabelling g es a.erase b.erase := by
  induction h with
  | single => exact .single _ _
  | cons turn tail ih => exact .cons (turn.erase g) ih
 theorem liftExpandedTurn {e f a b} (h : ExpandedTurn g e f a b) (event : Nat)
     (input : TaggedContext) (erased : input.erase=a) :
     ∃ output,TaggedExpandedTurn g event e f input output ∧ output.erase=b := by
  cases h with
  | ordinary turn =>
    obtain ⟨output,tagged,eq⟩ := liftTurn g turn event input erased
    exact ⟨output,.ordinary tagged,eq⟩
  | bindToCtx r a => exact ⟨input,.bindToCtx r input,erased⟩
  | funToArg r a => exact ⟨input,.funToArg r input,erased⟩
 theorem liftExpandedLabelling {es a b} (h : ExpandedLabelling g es a b) (event : Nat)
     (input : TaggedContext) (erased : input.erase=a) :
     ∃ output,TaggedExpandedLabelling g event es input output ∧ output.erase=b := by
  induction h generalizing event input with
  | single => exact ⟨input,.single event _ input,erased⟩
  | cons turn tail ih =>
    obtain ⟨middle,tagged,same⟩ := liftExpandedTurn g turn event input erased
    obtain ⟨output,rest,last⟩ := ih (event+1) middle same
    exact ⟨output,.cons tagged rest,last⟩

 theorem TaggedExpandedTurn.originsBefore {event e f a b} (h : TaggedExpandedTurn g event e f a b)
     (causal : OriginsBefore event a) : OriginsBefore (event+1) b := by
  cases h with
  | ordinary turn => exact turn.originsBefore causal
  | bindToCtx | funToArg =>
    intro tag present
    rcases causal tag present with ⟨level,address,same⟩ | ⟨j,same,lt⟩
    · exact Or.inl ⟨level,address,same⟩
    · exact Or.inr ⟨j,same,by omega⟩
 theorem TaggedExpandedTurn.no_copy {event e f a b} (h : TaggedExpandedTurn g event e f a b)
     (unique : UniqueOrigins a) (fresh : ¬TaggedContext.HasOrigin (.written event) a) : UniqueOrigins b := by
  cases h with
  | ordinary turn => exact turn.no_copy unique fresh
  | bindToCtx | funToArg => exact unique
 theorem TaggedExpandedLabelling.no_copy {event es a b} (h : TaggedExpandedLabelling g event es a b)
     (unique : UniqueOrigins a) (causal : OriginsBefore event a) : UniqueOrigins b := by
  induction h with
  | single => exact unique
  | cons turn tail ih => exact ih (turn.no_copy g unique causal.fresh) (turn.originsBefore g causal)

 theorem TaggedExpandedTurn.old_present {event e f a b} (h : TaggedExpandedTurn g event e f a b)
     (level address) (present : TaggedContext.HasOrigin (.input level address) b) :
     TaggedContext.HasOrigin (.input level address) a := by
  cases h with
  | ordinary turn => exact turn.old_present level address present
  | bindToCtx | funToArg => exact present
 theorem TaggedExpandedLabelling.old_present {event es a b} (h : TaggedExpandedLabelling g event es a b)
     (level address) (present : TaggedContext.HasOrigin (.input level address) b) :
     TaggedContext.HasOrigin (.input level address) a := by
  induction h with
  | single => exact present
  | cons turn tail ih => exact turn.old_present g level address (ih present)
 theorem TaggedExpandedTurn.rewrite_old {event e f a b} (h : TaggedExpandedTurn g event e f a b)
     (level address xs) (unique : UniqueOrigins a)
     (survives : TaggedContext.HasOrigin (.input level address) b) :
     TaggedExpandedTurn g event e f (TaggedContext.rewrite (.input level address) xs a)
       (TaggedContext.rewrite (.input level address) xs b) := by
  cases h with
  | ordinary turn => exact .ordinary (turn.rewrite_old level address xs unique survives)
  | bindToCtx r a => exact .bindToCtx r _
  | funToArg r a => exact .funToArg r _
 theorem TaggedExpandedLabelling.rewrite_old {event es a b} (h : TaggedExpandedLabelling g event es a b)
     (level address xs) (unique : UniqueOrigins a) (causal : OriginsBefore event a)
     (survives : TaggedContext.HasOrigin (.input level address) b) :
     TaggedExpandedLabelling g event es (TaggedContext.rewrite (.input level address) xs a)
       (TaggedContext.rewrite (.input level address) xs b) := by
  induction h with
  | single => exact .single _ _ _
  | cons turn tail ih =>
    have middle := tail.old_present g level address survives
    exact .cons (turn.rewrite_old g level address xs unique middle)
      (ih (turn.no_copy g unique causal.fresh) (turn.originsBefore g causal) survives)
private def TaggedInputInvariant (e : Endpoint g) (a b : TaggedContext) : Prop :=
  match e with | .inl ⟨n,_⟩ => TaggedProperInvariant (g.label n).sort a b | _ => True
private theorem taggedExpanded_proper {event e f a b} (h : TaggedExpandedTurn g event e f a b) :
    TaggedInputInvariant g e a b := by
  cases h with
  | ordinary turn =>
    cases turn with
    | node n p q rule => exact taggedTraversal_proper rule
    | transparent => trivial
  | bindToCtx r a => change TaggedProperInvariant (g.label r.lam).sort a a; rw [r.lamLabel]; rfl
  | funToArg r a => change TaggedProperInvariant (g.label r.app).sort a a; rw [r.appLabel]; rfl

 theorem TaggedExpandedTurn.rigid {event e f a b c d} (h : TaggedExpandedTurn g event e f a b)
     (k : TaggedExpandedTurn g event e f c d) (input : RigidContext a c) : RigidContext b d := by
  cases h with
  | ordinary turn =>
    cases k with
    | ordinary other => exact turn.rigid other input
    | bindToCtx r c =>
      have same := taggedExpanded_proper g (TaggedExpandedTurn.ordinary turn)
      change TaggedProperInvariant (g.label r.lam).sort _ _ at same
      rw [r.lamLabel] at same
      exact same ▸ input
    | funToArg r c =>
      have same := taggedExpanded_proper g (TaggedExpandedTurn.ordinary turn)
      change TaggedProperInvariant (g.label r.app).sort _ _ at same
      rw [r.appLabel] at same
      exact same ▸ input
  | bindToCtx r a =>
    have same := taggedExpanded_proper g k
    change TaggedProperInvariant (g.label r.lam).sort c d at same
    rw [r.lamLabel] at same
    exact same ▸ input
  | funToArg r a =>
    have same := taggedExpanded_proper g k
    change TaggedProperInvariant (g.label r.app).sort c d at same
    rw [r.appLabel] at same
    exact same ▸ input
 theorem TaggedExpandedLabelling.rigid {event es a b c d} (h : TaggedExpandedLabelling g event es a b)
     (k : TaggedExpandedLabelling g event es c d) (input : RigidContext a c) : RigidContext b d := by
  induction h generalizing c d with
  | single => cases k; exact input
  | cons turn tail ih => cases k with
    | cons other rest => exact ih rest (turn.rigid g other input)

 theorem expanded_old_marker_replay {es a b} (h : ExpandedLabelling g es a b) :
     ∃ output,TaggedExpandedLabelling g 0 es (TaggedContext.initial a) output ∧ output.erase=b ∧
       UniqueOrigins output ∧
       ∀ level address xs,TaggedContext.HasUnaryOrigin (.input level address) output →
         ExpandedLabelling g es (TaggedContext.rewrite (.input level address) xs (TaggedContext.initial a)).erase
           (TaggedContext.rewrite (.input level address) xs output).erase := by
  obtain ⟨output,tagged,erased⟩ := liftExpandedLabelling g h 0 _ (TaggedContext.initial_erase a)
  refine ⟨output,tagged,erased,tagged.no_copy g (TaggedContext.initial_unique a)
    (TaggedContext.initial_originsBefore a),?_⟩
  intro level address xs present
  exact (tagged.rewrite_old g level address xs (TaggedContext.initial_unique a)
    (TaggedContext.initial_originsBefore a) present.hasOrigin).erase g

 theorem expanded_written_marker_fixed {es a output}
     (h : TaggedExpandedLabelling g 0 es (TaggedContext.initial a) output)
     (level : Nat) (address : List Bool) (event : Nat) (shape : MarkerShape)
     (written : (output.get level).constructorAt address=some (.written event,shape))
     {c d} (other : ExpandedLabelling g es c d) : levelMarkerAt address (d.get level)=some shape := by
  obtain ⟨second,tagged,erased⟩ := liftExpandedLabelling g other 0 _ (TaggedContext.initial_erase c)
  have rigid := h.rigid g tagged (RigidContext.initial a c)
  have same := (rigid level).written_at address event shape written
  have visible := congrArg (Option.map Prod.snd) same
  rw [TaggedLevel.markerAt_erase] at visible
  change levelMarkerAt address (second.erase.get level)=some shape at visible
  simpa only [erased] using visible

 theorem expanded_free_tail_no_written {es a output}
     (h : TaggedExpandedLabelling g 0 es (TaggedContext.initial a) output) (width : Nat)
     (varies : ∀ tail : Context,∃ input,ExpandedLabelling g es input (output.erase.replace width tail))
     (level : Nat) (high : width≤level) (address : List Bool) (event : Nat) (shape : MarkerShape) :
     (output.get level).constructorAt address≠some (.written event,shape) := by
  intro written
  obtain ⟨input,labels⟩ := varies Context.empty
  have fixed := expanded_written_marker_fixed g h level address event shape written labels
  have emptyLevel : (output.erase.replace width Context.empty).get level=Level.empty := by
    simp [Context.replace,show ¬level<width by omega,Context.empty]
  rw [emptyLevel] at fixed
  cases address <;> simp [levelMarkerAt] at fixed
/-- The root occurrence of a given expanded independence theorem supplies
actual labelings with every terminal tail. No existence is inferred from a
vacuous assignment-dependent property. -/
theorem expanded_output_tail_varies {root : B} {es} (indep : ExpandedIndependenceOn g root es)
    {a b} (generated : GeneratedExpandedProperPath g root es) (labels : ExpandedLabelling g es a b)
    (last : Endpoint g) (width : Nat) (finish : es.getLast?=some last)
    (terminal : ExpandedTarget g root last width) :
    ∀ tail : Context,∃ input,ExpandedLabelling g es input (b.replace width tail) := by
  obtain ⟨cs,trace,first,lastCtx⟩ := labels.contextTrace g
  have atRoot : es[0]?=some (.inr (.inl root)) := by
    cases es <;> simpa using generated.rooted g
  have atContext : cs[0]?=some a := by
    cases cs with
    | nil => cases first
    | cons => exact first
  obtain ⟨_,_,_,_,_,sync⟩ := indep cs trace 0 (.inr (.inl root)) last a b 0 width false
    atRoot atContext finish lastCtx (.proper _ .root 0 .root True.intro) terminal
  intro tail
  obtain ⟨ds,next,_,newLast⟩ := sync tail
  cases ds with
  | nil => cases newLast
  | cons input rest => exact ⟨input,next.labelling g rfl newLast⟩

/-- The source3.5.6 high-tail exclusion is available for a generated typed
expanded path once its actual independence induction hypothesis is supplied. -/
theorem expanded_no_written_terminal_tail {root : B} {es} (indep : ExpandedIndependenceOn g root es)
    {a output} (generated : GeneratedExpandedProperPath g root es)
    (h : TaggedExpandedLabelling g 0 es (TaggedContext.initial a) output)
    (last : Endpoint g) (width : Nat) (finish : es.getLast?=some last)
    (terminal : ExpandedTarget g root last width)
    (level : Nat) (high : width≤level) (address : List Bool) (event : Nat) (shape : MarkerShape) :
    (output.get level).constructorAt address≠some (.written event,shape) := by
  have labels : ExpandedLabelling g es a output.erase := by simpa using h.erase g
  exact expanded_free_tail_no_written g h width
    (expanded_output_tail_varies g indep generated labels last width finish terminal)
    level high address event shape
end
end Lamping.AG.Marker





