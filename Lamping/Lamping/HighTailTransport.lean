import Lamping.Lamping.IndexedLevelBalance
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph

private def PackedBraOutput (index : Nat) : (kind : Kind) → Port kind → Port kind → Context → Prop
  | .op .bra,.inr _,.inl _,output => ∃ x y,output.get index=.pair x y
  | _,_,_,_ => True

private theorem packed_bra_output {index kind p q a b} (rule : Traversal index kind p q a b) :
    PackedBraOutput index kind p q b := by
  cases rule with
  | direct passage =>
    cases passage <;> try trivial
    case bra shell tail x y => exact ⟨x,y,by simp [Context.replace,Context.cons]⟩
  | inverse passage => cases passage <;> trivial

/-- The weak Bra bound would fail at equality: an arbitrary replacement at
the auxiliary height changes a child packed at the principal height. -/
theorem bra_equal_height_no_sync : ¬∀ replacement : Context,
    Traversal 0 (.op .bra) (.inr ()) (.inl ())
      (((Context.empty.cons (.star .empty)).cons .empty).replace 1 replacement)
      ((Context.empty.cons (.pair (.star .empty) .empty)).replace 0 replacement) := by
  intro synchronize
  obtain ⟨x,y,impossible⟩ := packed_bra_output (synchronize Context.empty)
  cases impossible

theorem bra_equal_height_actual : Traversal 0 (.op .bra) (.inr ()) (.inl ())
    ((Context.empty.cons (.star .empty)).cons .empty)
    (Context.empty.cons (.pair (.star .empty) .empty)) :=
  .direct (.bra Context.empty Context.empty (.star .empty) .empty)

namespace Context
private def prepend : List Level → Context → Context
  | [],tail => tail
  | x::xs,tail => (prepend xs tail).cons x

private theorem cons_replace_successor (a c : Context) (x : Level) (k : Nat) :
    (a.cons x).replace (k+1) c=(a.replace k c).cons x := by
  ext n
  cases n with
  | zero => simp [replace]
  | succ n => simp [replace,cons,show n+1<k+1 ↔ n<k by omega]

private theorem prepend_replace (xs : List Level) (tail replacement : Context) (k : Nat) :
    (prepend xs tail).replace (xs.length+k) replacement=prepend xs (tail.replace k replacement) := by
  induction xs with
  | nil => simp only [prepend,List.length_nil,Nat.zero_add]
  | cons x xs ih =>
    simp only [prepend,List.length_cons]
    rw [show xs.length+1+k=(xs.length+k)+1 by omega,cons_replace_successor,ih]

private theorem prepend_tail (xs : List Level) (tail : Context) (k : Nat) :
    (prepend xs tail).tail (xs.length+k)=tail.tail k := by
  induction xs with
  | nil => simp only [prepend,List.length_nil,Nat.zero_add]
  | cons x xs ih =>
    ext n
    have same := congrArg (fun c : Context => c.get n) ih
    change (prepend xs tail).get (xs.length+k+n)=tail.get (k+n) at same
    change ((prepend xs tail).cons x).get (xs.length+1+k+n)=tail.get (k+n)
    rw [show xs.length+1+k+n=(xs.length+k+n)+1 by omega]
    exact same

private theorem frame_tail (shell tail : Context) (xs : List Level) (i k : Nat) :
    (shell.replace i (prepend xs tail)).tail (i+xs.length+k)=tail.tail k := by
  have first : (shell.replace i (prepend xs tail)).tail (i+xs.length+k)=
      (prepend xs tail).tail (xs.length+k) := by
    ext n
    change (shell.replace i (prepend xs tail)).get (i+xs.length+k+n)=
      (prepend xs tail).get (xs.length+k+n)
    rw [replace_high _ _ (by omega)]
    congr 1; omega
  exact first.trans (prepend_tail xs tail k)

private theorem frame_replace (shell tail replacement : Context) (xs : List Level) (i k : Nat) :
    (shell.replace i (prepend xs tail)).replace (i+xs.length+k) replacement=
      shell.replace i (prepend xs (tail.replace k replacement)) := by
  rw [show i+xs.length+k=i+(xs.length+k) by omega,replace_nested,prepend_replace]
end Context

private theorem fanO_sync (shell tail : Context) (x : Level) (i k : Nat) :
    (shell.replace i (tail.cons x)).tail (i+1+k)=
      (shell.replace i (tail.cons (.o x))).tail (i+1+k) ∧
    ∀ replacement, Traversal i (.op .fan) fanO (.inl ())
      ((shell.replace i (tail.cons x)).replace (i+1+k) replacement)
      ((shell.replace i (tail.cons (.o x))).replace (i+1+k) replacement) := by
  have left := Context.frame_tail shell tail [x] i k
  have right := Context.frame_tail shell tail [.o x] i k
  constructor
  · exact left.trans right.symm
  · intro replacement
    have left := Context.frame_replace shell tail replacement [x] i k
    have right := Context.frame_replace shell tail replacement [.o x] i k
    simp only [Context.prepend,List.length_cons,List.length_nil] at left right
    rw [left,right]
    exact .direct (.fanO shell (tail.replace k replacement) x)

private theorem fanStar_sync (shell tail : Context) (x : Level) (i k : Nat) :
    (shell.replace i (tail.cons x)).tail (i+1+k)=
      (shell.replace i (tail.cons (.star x))).tail (i+1+k) ∧
    ∀ replacement, Traversal i (.op .fan) fanStar (.inl ())
      ((shell.replace i (tail.cons x)).replace (i+1+k) replacement)
      ((shell.replace i (tail.cons (.star x))).replace (i+1+k) replacement) := by
  have left := Context.frame_tail shell tail [x] i k
  have right := Context.frame_tail shell tail [.star x] i k
  constructor
  · exact left.trans right.symm
  · intro replacement
    have left := Context.frame_replace shell tail replacement [x] i k
    have right := Context.frame_replace shell tail replacement [.star x] i k
    simp only [Context.prepend,List.length_cons,List.length_nil] at left right
    rw [left,right]
    exact .direct (.fanStar shell (tail.replace k replacement) x)

private theorem cro_sync (shell tail : Context) (i k : Nat) :
    (shell.replace i tail).tail (i+k)=
      (shell.replace i (tail.cons .empty)).tail (i+1+k) ∧
    ∀ replacement, Traversal i (.op .cro) (.inr ()) (.inl ())
      ((shell.replace i tail).replace (i+k) replacement)
      ((shell.replace i (tail.cons .empty)).replace (i+1+k) replacement) := by
  have left := Context.frame_tail shell tail [] i k
  have right := Context.frame_tail shell tail [.empty] i k
  constructor
  · exact left.trans right.symm
  · intro replacement
    have left := Context.frame_replace shell tail replacement [] i k
    have right := Context.frame_replace shell tail replacement [.empty] i k
    simp only [Context.prepend,List.length_cons,List.length_nil] at left right
    rw [Nat.add_zero] at left
    rw [left,right]
    exact .direct (.cro shell (tail.replace k replacement))

private theorem bra_sync (shell tail : Context) (x y : Level) (i k : Nat) :
    (shell.replace i ((tail.cons x).cons y)).tail (i+2+k)=
      (shell.replace i (tail.cons (.pair x y))).tail (i+1+k) ∧
    ∀ replacement, Traversal i (.op .bra) (.inr ()) (.inl ())
      ((shell.replace i ((tail.cons x).cons y)).replace (i+2+k) replacement)
      ((shell.replace i (tail.cons (.pair x y))).replace (i+1+k) replacement) := by
  have left := Context.frame_tail shell tail [y,x] i k
  have right := Context.frame_tail shell tail [.pair x y] i k
  constructor
  · exact left.trans right.symm
  · intro replacement
    have left := Context.frame_replace shell tail replacement [y,x] i k
    have right := Context.frame_replace shell tail replacement [.pair x y] i k
    simp only [Context.prepend,List.length_cons,List.length_nil] at left right
    rw [left,right]
    exact .direct (.bra shell (tail.replace k replacement) x y)

/-- One actual forward-oriented primitive preserves a sufficiently high
tail. An app context→argument turn loses one additional old level because
the context is unchanged while the geometric height rises by one. The extra
parameter accommodates the losses of a later continuation. -/
theorem Traversal.high_tail_sync {index kind p q a b}
    (rule : Traversal index kind p q a b) (base : Int) (m n : Nat)
    (bounded : ControlIndexBound (⟨kind,index⟩ : Label signature) base)
    (source : portDepth index kind base p=(m : Int))
    (target : portDepth index kind base q=(n : Int))
    (forward : ForwardPorts kind p q) (extra : Nat) :
    ∃ loss : Nat, a.tail (m+loss+extra)=b.tail (n+extra) ∧
      ∀ replacement, Traversal index kind p q
        (a.replace (m+loss+extra) replacement) (b.replace (n+extra) replacement) := by
  cases rule with
  | direct passage =>
    cases passage with
    | fanO shell tail x =>
      change (index : Int)<base at bounded
      change base=(m : Int) at source
      change base=(n : Int) at target
      have same : m=n := by omega
      subst n
      have width : m+extra=index+1+(m+extra-index-1) := by omega
      have sync := fanO_sync shell tail x index (m+extra-index-1)
      exact ⟨0,by simpa only [Nat.add_zero,←width] using sync.1,
        by simpa only [Nat.add_zero,←width] using sync.2⟩
    | fanStar shell tail x =>
      change (index : Int)<base at bounded
      change base=(m : Int) at source
      change base=(n : Int) at target
      have same : m=n := by omega
      subst n
      have width : m+extra=index+1+(m+extra-index-1) := by omega
      have sync := fanStar_sync shell tail x index (m+extra-index-1)
      exact ⟨0,by simpa only [Nat.add_zero,←width] using sync.1,
        by simpa only [Nat.add_zero,←width] using sync.2⟩
    | cro shell tail =>
      change (index : Int)≤base at bounded
      change base=(m : Int) at source
      change base+1=(n : Int) at target
      have src : m+extra=index+(m+extra-index) := by omega
      have dst : n+extra=index+1+(m+extra-index) := by omega
      have sync := cro_sync shell tail index (m+extra-index)
      exact ⟨0,by simpa only [Nat.add_zero,←src,←dst] using sync.1,
        by simpa only [Nat.add_zero,←src,←dst] using sync.2⟩
    | bra shell tail x y =>
      change (index : Int)<base at bounded
      change base+1=(m : Int) at source
      change base=(n : Int) at target
      have src : m+extra=index+2+(n+extra-index-1) := by omega
      have dst : n+extra=index+1+(n+extra-index-1) := by omega
      have sync := bra_sync shell tail x y index (n+extra-index-1)
      exact ⟨0,by simpa only [Nat.add_zero,←src,←dst] using sync.1,
        by simpa only [Nat.add_zero,←src,←dst] using sync.2⟩
    | appFun input =>
      change (index : Int)=(m : Int) at source
      change (index : Int)=(n : Int) at target
      have same : m=n := by omega
      subst n
      exact ⟨0,rfl,fun replacement => .direct (.appFun _)⟩
    | appArg input =>
      change (index : Int)=(m : Int) at source
      change (index : Int)+1=(n : Int) at target
      have same : n=m+1 := by omega
      subst n
      exact ⟨1,rfl,fun replacement => .direct (.appArg _)⟩
    | lamBody input =>
      change (index : Int)=(m : Int) at source
      change (index : Int)=(n : Int) at target
      have same : m=n := by omega
      subst n
      exact ⟨0,rfl,fun replacement => .direct (.lamBody _)⟩
  | inverse passage =>
    cases passage with
    | fanO shell tail x =>
      change (index : Int)<base at bounded
      change base=(m : Int) at source
      change base=(n : Int) at target
      have same : m=n := by omega
      subst n
      have width : m+extra=index+1+(m+extra-index-1) := by omega
      have sync := fanO_sync shell tail x index (m+extra-index-1)
      refine ⟨0,by simpa only [Nat.add_zero,←width] using sync.1.symm,?_⟩
      intro replacement
      simpa only [Nat.add_zero,←width] using (sync.2 replacement).reverse
    | fanStar shell tail x =>
      change (index : Int)<base at bounded
      change base=(m : Int) at source
      change base=(n : Int) at target
      have same : m=n := by omega
      subst n
      have width : m+extra=index+1+(m+extra-index-1) := by omega
      have sync := fanStar_sync shell tail x index (m+extra-index-1)
      refine ⟨0,by simpa only [Nat.add_zero,←width] using sync.1.symm,?_⟩
      intro replacement
      simpa only [Nat.add_zero,←width] using (sync.2 replacement).reverse
    | cro shell tail =>
      change (index : Int)≤base at bounded
      change base+1=(m : Int) at source
      change base=(n : Int) at target
      have src : m+extra=index+1+(n+extra-index) := by omega
      have dst : n+extra=index+(n+extra-index) := by omega
      have sync := cro_sync shell tail index (n+extra-index)
      refine ⟨0,by simpa only [Nat.add_zero,←src,←dst] using sync.1.symm,?_⟩
      intro replacement
      simpa only [Nat.add_zero,←src,←dst] using (sync.2 replacement).reverse
    | bra shell tail x y =>
      change (index : Int)<base at bounded
      change base=(m : Int) at source
      change base+1=(n : Int) at target
      have src : m+extra=index+1+(m+extra-index-1) := by omega
      have dst : n+extra=index+2+(m+extra-index-1) := by omega
      have sync := bra_sync shell tail x y index (m+extra-index-1)
      refine ⟨0,by simpa only [Nat.add_zero,←src,←dst] using sync.1.symm,?_⟩
      intro replacement
      simpa only [Nat.add_zero,←src,←dst] using (sync.2 replacement).reverse
    | appFun input => cases forward.1
    | appArg input => cases forward.1
    | lamBody input => cases forward.1

private theorem Traversal.target_depth_nonnegative {index kind p q a b}
    (rule : Traversal index kind p q a b) (base : Int)
    (bounded : ControlIndexBound (⟨kind,index⟩ : Label signature) base) :
    0≤portDepth index kind base q := by
  cases rule with
  | direct passage => cases passage <;> simp_all [ControlIndexBound,portDepth,appArg,lamBody] <;> omega
  | inverse passage => cases passage <;> simp_all [ControlIndexBound,portDepth,appCtx] <;> omega

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Int}

/-- Actual finite ordinary paths in an indexed balanced graph have a common
high tail and admit synchronous replacement there. The width can grow at
internal application-argument turns; it is not fixed to the source height.
This theorem makes no arbitrary replacement claim at a smaller source index. -/
theorem Labelling.high_tail_sync {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b) (balance : IndexedLevelBalance g boundary) (fw : Forward g es)
    (m n : Nat)
    (first : ∀ e,es.head?=some e → endpointDepth g balance.nodes boundary balance.vertices e=(m : Int))
    (last : ∀ e,es.getLast?=some e → endpointDepth g balance.nodes boundary balance.vertices e=(n : Int)) :
    ∃ width : Nat,m≤width ∧ a.tail width=b.tail n ∧
      ∀ replacement,Labelling g es (a.replace width replacement) (b.replace n replacement) := by
  induction labels generalizing m with
  | single e a =>
    have same : m=n := by have left := first e rfl; have right := last e rfl; omega
    subst n
    exact ⟨m,Nat.le_refl _,rfl,fun replacement => .single _ _⟩
  | @cons e f es a middle b turn rest ih =>
    have restLast : ∀ x,(f::es).getLast?=some x →
        endpointDepth g balance.nodes boundary balance.vertices x=(n : Int) := by
      intro x finish
      exact last x (by simpa only [List.getLast?_cons_cons] using finish)
    cases fw with
    | node node p q arrives leaves direction restForward =>
      have actual := turn
      rw [arrives,leaves] at actual
      cases actual with
      | node node p q rule =>
        have source : portDepth (g.label node).index (g.label node).sort (balance.nodes node) p=(m : Int) := by
          change endpointDepth g balance.nodes boundary balance.vertices (.inl ⟨node,p⟩)=(m : Int)
          rw [←arrives,balance.wiring]
          exact first e rfl
        have nonnegative := rule.target_depth_nonnegative (balance.nodes node) (balance.bounded node)
        let next := (portDepth (g.label node).index (g.label node).sort (balance.nodes node) q).toNat
        have target : portDepth (g.label node).index (g.label node).sort (balance.nodes node) q=(next : Int) := by
          dsimp only [next]; omega
        have nextFirst : ∀ x,(f::es).head?=some x →
            endpointDepth g balance.nodes boundary balance.vertices x=(next : Int) := by
          intro x head
          have same := Option.some.inj head
          subst x
          rw [leaves]
          exact target
        obtain ⟨width,bounded,tailEq,tailSync⟩ := ih restForward next nextFirst restLast
        have widthEq : width=next+(width-next) := by omega
        obtain ⟨loss,localEq,localSync⟩ := rule.high_tail_sync (balance.nodes node) m next
          (balance.bounded node) source target direction (width-next)
        rw [←widthEq] at localEq localSync
        refine ⟨m+loss+(width-next),by omega,localEq.trans tailEq,?_⟩
        intro replacement
        apply Labelling.cons
        · rw [arrives,leaves]
          exact .node node p q (localSync replacement)
        · exact tailSync replacement
    | transparent vertex direction arrives leaves restForward =>
      have actual := turn
      rw [arrives,leaves] at actual
      cases actual
      have source : endpointDepth g balance.nodes boundary balance.vertices
          (.inr (.inr (vertex,direction)))=(m : Int) := by
        rw [←arrives,balance.wiring]
        exact first e rfl
      have nextFirst : ∀ x,(f::es).head?=some x →
          endpointDepth g balance.nodes boundary balance.vertices x=(m : Int) := by
        intro x head
        have same := Option.some.inj head
        subst x
        rw [leaves]
        exact source
      obtain ⟨width,bounded,tailEq,tailSync⟩ := ih restForward m nextFirst restLast
      refine ⟨width,bounded,tailEq,?_⟩
      intro replacement
      apply Labelling.cons
      · rw [arrives,leaves]
        exact .transparent vertex direction _
      · exact tailSync replacement
end

namespace ProperRole
def departureHeight (role : ProperRole) (index : Nat) : Nat :=
  if role=.appArg then index+1 else index
end ProperRole

private theorem role_port_depth (actual : Label signature) (op : Op) (index : Nat) (base : Int)
    (p : Port actual.sort) (canonical : Port (.op op))
    (lab : actual=label op index) (role : HEq p canonical) :
    portDepth actual.index actual.sort base p=portDepth index (.op op) base canonical := by
  subst actual
  have same : p=canonical := eq_of_heq role
  subst p
  rfl

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Int}

theorem AtProperRole.outgoing_depth (balance : IndexedLevelBalance g boundary)
    (root : B) (rootDepth : boundary root=0) {e role index}
    (atPort : AtProperRole g root e role index) (outgoing : role.outgoing) :
    endpointDepth g balance.nodes boundary balance.vertices e=(role.departureHeight index : Int) := by
  cases atPort with
  | root => exact rootDepth
  | appCtx node p index lab port => exact False.elim outgoing
  | appFun node p index lab port =>
    exact role_port_depth (g.label node) .app index (balance.nodes node) p (.inl ()) lab port
  | appArg node p index lab port =>
    simpa [ProperRole.departureHeight,portDepth,AG.appArg] using
      role_port_depth (g.label node) .app index (balance.nodes node) p AG.appArg lab port
  | lamCtx node p index lab port => exact False.elim outgoing
  | lamBody node p index lab port =>
    exact role_port_depth (g.label node) .lam index (balance.nodes node) p AG.lamBody lab port
  | lamBind node p index lab port => exact False.elim outgoing

theorem AtProperRole.incoming_depth (balance : IndexedLevelBalance g boundary)
    (root : B) {e role index} (atPort : AtProperRole g root e role index) (incoming : role.incoming) :
    endpointDepth g balance.nodes boundary balance.vertices e=(role.terminalWidth index : Int) := by
  cases atPort with
  | root => exact False.elim incoming
  | appCtx node p index lab port =>
    exact role_port_depth (g.label node) .app index (balance.nodes node) p AG.appCtx lab port
  | appFun node p index lab port => exact False.elim incoming
  | appArg node p index lab port => exact False.elim incoming
  | lamCtx node p index lab port =>
    exact role_port_depth (g.label node) .lam index (balance.nodes node) p (.inl ()) lab port
  | lamBody node p index lab port => exact False.elim incoming
  | lamBind node p index lab port =>
    simpa [ProperRole.terminalWidth,portDepth,AG.lamBind] using
      role_port_depth (g.label node) .lam index (balance.nodes node) p AG.lamBind lab port

/-- The entire tail/strict-width/synchronization component of ordinary
Independence follows from actual indexed balance. Arbitrary replacement at
the smaller source index remains a separate existence obligation. -/
theorem IndexedLevelBalance.independence_tail (balance : IndexedLevelBalance g boundary)
    (root : B) (rootDepth : boundary root=0)
    (es : List (Endpoint g)) (e f : Endpoint g) (sr tr : ProperRole) (m n : Nat) (a b : Context)
    (first : es.head?=some e) (finish : es.getLast?=some (g.wire f))
    (atSource : AtProperRole g root e sr m) (outgoing : sr.outgoing)
    (atTarget : AtProperRole g root f tr n) (incoming : tr.incoming)
    (fw : Forward g es) (labels : Labelling g es a b) :
    ∃ width,m≤width ∧ (sr=.appArg → m<width) ∧
      (∀ c,b=b.replace (tr.terminalWidth n) c → a=a.replace width c) ∧
      ∀ c,Labelling g es (a.replace width c) (b.replace (tr.terminalWidth n) c) := by
  obtain ⟨width,lower,tailEq,synchronize⟩ := labels.high_tail_sync balance fw
    (sr.departureHeight m) (tr.terminalWidth n)
    (by intro x head; rw [first] at head; cases Option.some.inj head
        exact atSource.outgoing_depth balance root rootDepth outgoing)
    (by intro x last; rw [finish] at last; cases Option.some.inj last
        rw [balance.wiring]; exact atTarget.incoming_depth balance root incoming)
  refine ⟨width,?_,?_,?_,synchronize⟩
  · dsimp only [ProperRole.departureHeight] at lower
    split at lower <;> omega
  · intro argument
    subst sr
    change m+1≤width at lower
    omega
  · intro c fixed
    have targetTail := (Context.replace_fixed_iff_tail b c (tr.terminalWidth n)).mp fixed
    exact (Context.replace_fixed_iff_tail a c width).mpr (tailEq.trans targetTail)
end
end Lamping.AG





