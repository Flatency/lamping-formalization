import Lamping.Lamping.MarkerProvenance
namespace Lamping.AG.Marker
open Graph Lambda
namespace TaggedContext

def HasOrigin (tag : Origin) (a : TaggedContext) : Prop := ∃ k, tag ∈ (a.get k).origins

 theorem hasOrigin_cons (tag : Origin) (a : TaggedContext) (x : TaggedLevel) :
    HasOrigin tag (a.cons x) ↔ tag∈x.origins ∨ HasOrigin tag a := by
  constructor
  · rintro ⟨k,hk⟩
    cases k with
    | zero => exact Or.inl hk
    | succ k => exact Or.inr ⟨k,hk⟩
  · rintro (hx | ⟨k,hk⟩)
    · exact ⟨0,hx⟩
    · exact ⟨k+1,hk⟩

 theorem hasOrigin_replace (tag : Origin) (a b : TaggedContext) (n : Nat) :
    HasOrigin tag (a.replace n b) ↔
      (∃ k, k<n ∧ tag∈(a.get k).origins) ∨ HasOrigin tag b := by
  constructor
  · rintro ⟨k,hk⟩
    by_cases low : k<n
    · exact Or.inl ⟨k,low,by simpa only [replace,if_pos low] using hk⟩
    · exact Or.inr ⟨k-n,by simpa only [replace,if_neg low] using hk⟩
  · rintro (⟨k,low,hk⟩ | ⟨k,hk⟩)
    · exact ⟨k,by simpa only [replace,if_pos low] using hk⟩
    · refine ⟨n+k,?_⟩
      simpa only [replace,if_neg (by omega : ¬n+k<n),Nat.add_sub_cancel_left] using hk

 theorem initial_no_written (a : Context) (event : Nat) :
    ¬HasOrigin (.written event) (initial a) := by
  rintro ⟨k,hk⟩
  exact TaggedLevel.initial_no_written k [] (a.get k) event hk
end TaggedContext

/-- A direct passage retains every old origin; its only possible new origin
is its one named constructor. This is causal membership, not yet no-duplication. -/
theorem TaggedPassage.origin_membership {origin i k p q a b}
    (h : TaggedPassage origin i k p q a b) :
    (∀ tag, TaggedContext.HasOrigin tag a → TaggedContext.HasOrigin tag b) ∧
    (∀ tag, TaggedContext.HasOrigin tag b → tag=origin ∨ TaggedContext.HasOrigin tag a) := by
  cases h <;>
    (try simp only [TaggedContext.hasOrigin_replace,TaggedContext.hasOrigin_cons,
      TaggedLevel.origins,List.mem_cons,List.mem_append,List.not_mem_nil]) <;> grind

 theorem TaggedTraversal.origin_membership {event i k p q a b}
    (h : TaggedTraversal event i k p q a b) (tag : Origin)
    (present : TaggedContext.HasOrigin tag b) :
    tag=.written event ∨ TaggedContext.HasOrigin tag a := by
  cases h with
  | direct step => exact step.origin_membership.2 tag present
  | inverse origin step => exact Or.inr (step.origin_membership.1 tag present)

/-- Future event names cannot arise before their actual turn. Input markers
remain distinguished from all writes even when their erased symbols agree. -/
def OriginsBefore (event : Nat) (a : TaggedContext) : Prop :=
  ∀ tag, TaggedContext.HasOrigin tag a →
    (∃ level address, tag=.input level address) ∨ ∃ turn, tag=.written turn ∧ turn<event

 theorem TaggedContext.initial_originsBefore (a : Context) : OriginsBefore 0 (TaggedContext.initial a) := by
  intro tag present
  cases tag with
  | input level address => exact Or.inl ⟨level,address,rfl⟩
  | written event => exact False.elim (TaggedContext.initial_no_written a event present)

 theorem TaggedTraversal.originsBefore {event i k p q a b}
    (h : TaggedTraversal event i k p q a b) (old : OriginsBefore event a) : OriginsBefore (event+1) b := by
  intro tag present
  rcases h.origin_membership tag present with current | previous
  · exact Or.inr ⟨event,current,by omega⟩
  · rcases old tag previous with input | ⟨turn,same,lower⟩
    · exact Or.inl input
    · exact Or.inr ⟨turn,same,by omega⟩


/-- Only forward fan or bracket passages introduce a marker constructor. -/
def WriteKind : (kind : Kind) → Port kind → Port kind → Prop
  | .op .fan,.inr _,.inl _ => True
  | .op .bra,.inr _,.inl _ => True
  | _,_,_ => False

 theorem TaggedPassage.new_origin_requires_write {origin i k p q a b}
    (h : TaggedPassage origin i k p q a b)
    (present : TaggedContext.HasOrigin origin b)
    (absent : ¬TaggedContext.HasOrigin origin a) : WriteKind k p q := by
  cases h <;>
    (try simp only [WriteKind,TaggedContext.hasOrigin_replace,TaggedContext.hasOrigin_cons,
      TaggedLevel.origins,List.mem_cons,List.mem_append,List.not_mem_nil] at *) <;> grind

 theorem TaggedTraversal.new_origin {event i k p q a b} (h : TaggedTraversal event i k p q a b)
    (writer : Nat) (present : TaggedContext.HasOrigin (.written writer) b)
    (absent : ¬TaggedContext.HasOrigin (.written writer) a) : writer=event ∧ WriteKind k p q := by
  cases h with
  | direct step =>
    have same : Origin.written writer=.written event :=
      (step.origin_membership.2 _ present).resolve_right absent
    have eq := Origin.written.inj same
    subst writer
    exact ⟨rfl,step.new_origin_requires_write present absent⟩
  | inverse origin step => exact False.elim (absent (step.origin_membership.1 _ present))

 theorem OriginsBefore.fresh {event : Nat} {a : TaggedContext} (h : OriginsBefore event a) :
    ¬TaggedContext.HasOrigin (.written event) a := by
  intro present
  rcases h _ present with ⟨level,address,same⟩ | ⟨turn,same,lower⟩
  · cases same
  · have eq := Origin.written.inj same
    omega
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

 theorem TaggedTurn.originsBefore {event e f a b} (h : TaggedTurn g event e f a b)
    (old : OriginsBefore event a) : OriginsBefore (event+1) b := by
  cases h with
  | node n p q rule => exact rule.originsBefore old
  | transparent w d a =>
    intro tag present
    rcases old tag present with input | ⟨turn,same,lower⟩
    · exact Or.inl input
    · exact Or.inr ⟨turn,same,by omega⟩

 theorem TaggedLabelling.originsBefore {event es a b} (h : TaggedLabelling g event es a b)
    (old : OriginsBefore event a) : OriginsBefore (event+es.length-1) b := by
  induction h with
  | single => simpa using old
  | @cons event e f es a b c turn tail ih =>
    have next := ih (turn.originsBefore old)
    have eq : event+(e::f::es).length-1=event+1+(f::es).length-1 := by
      simp only [List.length_cons]
      omega
    rw [eq]
    exact next

/-- The real labelled path always admits an erased-correct lift in which
every surviving marker names either an original input occurrence or an earlier
actual turn. Writer uniqueness/no-copy and replay are separate later theorems. -/
theorem path_origin_attribution {es a b} (h : Labelling g es a b) :
    ∃ output, TaggedLabelling g 0 es (TaggedContext.initial a) output ∧ output.erase=b ∧
      OriginsBefore (es.length-1) output := by
  obtain ⟨output,tagged,erased⟩ := initial_lift g h
  exact ⟨output,tagged,erased,by simpa using tagged.originsBefore (TaggedContext.initial_originsBefore a)⟩

/-- A writer is checked against the real arriving and departing node ports. -/
def WriterTurn (e f : Endpoint g) : Prop :=
  ∃ (n : N) (p q : Port (g.label n).sort),
    e=.inl ⟨n,p⟩ ∧ f=.inl ⟨n,q⟩ ∧ WriteKind (g.label n).sort p q

/-- The ordinal names a concrete turn position of the original path. -/
inductive WriterAt (writer : Nat) : Nat → List (Endpoint g) → Prop
  | here (event : Nat) (e f : Endpoint g) (es : List (Endpoint g))
      (same : writer=event) (writes : WriterTurn (g.wire e) f) : WriterAt writer event (e::f::es)
  | later {event : Nat} {e f : Endpoint g} {es : List (Endpoint g)}
      (tail : WriterAt writer (event+1) (f::es)) : WriterAt writer event (e::f::es)

 theorem TaggedTurn.new_origin {event e f a b} (h : TaggedTurn g event e f a b)
    (writer : Nat) (present : TaggedContext.HasOrigin (.written writer) b)
    (absent : ¬TaggedContext.HasOrigin (.written writer) a) :
    writer=event ∧ WriterTurn e f := by
  cases h with
  | node n p q rule =>
    obtain ⟨same,kind⟩ := rule.new_origin writer present absent
    exact ⟨same,n,p,q,rfl,rfl,kind⟩
  | transparent w d a => exact False.elim (absent present)

 theorem TaggedLabelling.writer_or_input {event es a b} (h : TaggedLabelling g event es a b)
    (writer : Nat) (present : TaggedContext.HasOrigin (.written writer) b) :
    TaggedContext.HasOrigin (.written writer) a ∨ WriterAt writer event es := by
  classical
  induction h with
  | single => exact Or.inl present
  | @cons event e f es a b c turn tail ih =>
    rcases ih present with oldMiddle | writerTail
    · by_cases oldInput : TaggedContext.HasOrigin (.written writer) a
      · exact Or.inl oldInput
      · obtain ⟨same,kind⟩ := turn.new_origin writer oldMiddle oldInput
        exact Or.inr (.here event e f es same kind)
    · exact Or.inr (.later writerTail)

 theorem WriterAt.range {writer event es} (h : WriterAt (g:=g) writer event es) :
    event≤writer ∧ writer<event+es.length-1 := by
  induction h with
  | here event e f es same kind => simp only [List.length_cons]; omega
  | later tail ih => simp only [List.length_cons] at *; omega

/-- Every surviving written marker has a real earlier fan/bracket writer at
its unique ordinal. This strengthens causal membership to physical-path provenance. -/
theorem actual_writer_attribution {es a b} (h : Labelling g es a b) :
    ∃ output, TaggedLabelling g 0 es (TaggedContext.initial a) output ∧ output.erase=b ∧
      ∀ writer, TaggedContext.HasOrigin (.written writer) output → WriterAt writer 0 es := by
  obtain ⟨output,tagged,erased⟩ := initial_lift g h
  refine ⟨output,tagged,erased,?_⟩
  intro writer present
  rcases tagged.writer_or_input writer present with impossible | actual
  · exact False.elim (TaggedContext.initial_no_written a writer impossible)
  · exact actual

/-- The numeric provenance resolves to exactly the original two physical
segment occurrences, including repeated traversals of the same edge. -/
theorem WriterAt.position {writer event es} (h : WriterAt (g:=g) writer event es) :
    ∃ e f, es[writer-event]?=some e ∧ es[writer-event+1]?=some f ∧ WriterTurn (g.wire e) f := by
  induction h with
  | here event e f es same writes =>
    subst writer
    exact ⟨e,f,by simp,by simp,writes⟩
  | @later event e f es tail ih =>
    obtain ⟨x,y,hx,hy,writes⟩ := ih
    have lower := tail.range.1
    have diff : writer-event=(writer-(event+1))+1 := by omega
    refine ⟨x,y,?_,?_,writes⟩
    · simpa only [diff,List.getElem?_cons_succ] using hx
    · simpa only [diff,List.getElem?_cons_succ] using hy

theorem WriterAt.unique_endpoints {writer event es} (_h : WriterAt (g:=g) writer event es)
    {e f e' f' : Endpoint g}
    (atE : es[writer-event]?=some e) (atF : es[writer-event+1]?=some f)
    (atE' : es[writer-event]?=some e') (atF' : es[writer-event+1]?=some f') : e=e' ∧ f=f' :=
  ⟨Option.some.inj (atE.symm.trans atE'),Option.some.inj (atF.symm.trans atF')⟩
end
end Lamping.AG.Marker




