import Lamping.Lamping.ExpandedPaths
import Lamping.Lamping.PathSplicing
namespace Lamping.AG
open Graph
/-- A local crossing uses the actual rule Net. No target transport is an input. -/
structure LocalPath {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    (g : Net signature N B W) (x y : B) (a b : Context) where
  edges : List (Endpoint g)
  start : edges.head?=some (.inr (.inl x))
  finish : edges.getLast?=some (g.wire (.inr (.inl y)))
  labeling : Labelling g edges a b
/-- The three-segment route through a rule's actual principal edge. -/
def leftRoute (f h : Op) (i j : Nat) (x : Aux f) (y : Aux h) :
    List (Endpoint (leftNet f h i j)) :=
  [.inr (.inl (.inl x)), .inl ⟨.inl (),.inl ()⟩, .inl ⟨.inr (),.inr y⟩]
/-- Each schema's left crossing is derived from the two local context relations. -/
def leftRoutePath (f h : Op) (i j : Nat) (x : Aux f) (y : Aux h)
    (a b c : Context)
    (p : Traversal i (.op f) (.inr x) (.inl ()) a b)
    (q : Traversal j (.op h) (.inl ()) (.inr y) b c) :
    LocalPath (leftNet f h i j) (.inl x) (.inr y) a c where
  edges := leftRoute f h i j x y
  start := rfl
  finish := rfl
  labeling := .cons (LabelledTurn.node (g:=leftNet f h i j) (.inl ()) (.inr x) (.inl ()) p)
    (.cons (LabelledTurn.node (g:=leftNet f h i j) (.inr ()) (.inl ()) (.inr y) q) (.single _ _))
/-- A cancellation target consists of one real segment, preserving the context. -/
def wirePath {A B : Type} [FiniteNames A] [FiniteNames B] (e : Bij A B)
    (x : A) (a : Context) : LocalPath (wires A B e) (.inl x) (.inr (e x)) a a where
  edges := [.inr (.inl (.inl x))]
  start := rfl
  finish := by simpa only [List.getLast?_cons, List.getLast?_nil, Option.or_none] using congrArg (fun y => some (Sum.inr (Sum.inl (Sum.inl y)) : Endpoint (wires A B e))) (e.left_inv x).symm
  labeling := .single _ _
/-- Fan annihilation: each named branch, with arbitrary context tail/shell. -/
def fanCancelLeft (i : Nat) (b : Bool) (shell tail : Context) (x : Level) :
    LocalPath (Schema.fanCancel i).left (.inl b) (.inr b)
      (shell.replace i (tail.cons x)) (shell.replace i (tail.cons x)) := by
  cases b
  · exact leftRoutePath .fan .fan i i false false _ _ _
      (.direct (.fanO shell tail x)) (.inverse (.fanO shell tail x))
  · exact leftRoutePath .fan .fan i i true true _ _ _
      (.direct (.fanStar shell tail x)) (.inverse (.fanStar shell tail x))
def fanCancelRight (i : Nat) (b : Bool) (a : Context) :
    LocalPath (Schema.fanCancel i).right.net (.inl b) (.inr b) a a :=
  wirePath (Bij.refl _) b a
/-- Cro and Bra annihilation are checked with their distinct printed transformations. -/
def croCancelLeft (i : Nat) (shell tail : Context) :
    LocalPath (Schema.croCancel i).left (.inl ()) (.inr ())
      (shell.replace i tail) (shell.replace i tail) :=
  leftRoutePath .cro .cro i i () () _ _ _
    (.direct (.cro shell tail)) (.inverse (.cro shell tail))
def croCancelRight (i : Nat) (a : Context) :
    LocalPath (Schema.croCancel i).right.net (.inl ()) (.inr ()) a a :=
  wirePath (Bij.refl _) () a
def braCancelLeft (i : Nat) (shell tail : Context) (x y : Level) :
    LocalPath (Schema.braCancel i).left (.inl ()) (.inr ())
      (shell.replace i ((tail.cons x).cons y)) (shell.replace i ((tail.cons x).cons y)) :=
  leftRoutePath .bra .bra i i () () _ _ _
    (.direct (.bra shell tail x y)) (.inverse (.bra shell tail x y))
def braCancelRight (i : Nat) (a : Context) :
    LocalPath (Schema.braCancel i).right.net (.inl ()) (.inr ()) a a :=
  wirePath (Bij.refl _) () a
/-- Beta's forward context-to-body route, distinct from binding-to-argument expansion. -/
def betaLeft (i : Nat) (a : Context) :
    LocalPath (Schema.beta i).left (.inl false) (.inr true) a a :=
  leftRoutePath .app .lam i i false true a a a (.direct (.appFun a)) (.direct (.lamBody a))
def betaRight (i : Nat) (a : Context) :
    LocalPath (Schema.beta i).right.net (.inl false) (.inr true) a a :=
  wirePath boolFlip false a
end Lamping.AG


namespace Lamping.AG
/-- Shift a complete passage above an arbitrary finite lower shell. This handles every
 passive operator, including passive controls, without a lookup table. -/
theorem Passage.lift {k kind p q a b} (h : Passage k kind p q a b)
    (s : Context) (n : Nat) :
    Passage (n+k) kind p q (s.replace n a) (s.replace n b) := by
  cases h with
  | fanO t u x => simpa only [Context.replace_nested] using Passage.fanO (i:=n+k) (s.replace n t) u x
  | fanStar t u x => simpa only [Context.replace_nested] using Passage.fanStar (i:=n+k) (s.replace n t) u x
  | cro t u => simpa only [Context.replace_nested] using Passage.cro (i:=n+k) (s.replace n t) u
  | bra t u x y => simpa only [Context.replace_nested] using Passage.bra (i:=n+k) (s.replace n t) u x y
  | appFun a => exact .appFun _
  | appArg a => exact .appArg _
  | lamBody a => exact .lamBody _
theorem Traversal.lift {k kind p q a b} (h : Traversal k kind p q a b)
    (s : Context) (n : Nat) :
    Traversal (n+k) kind p q (s.replace n a) (s.replace n b) := by
  cases h with
  | direct h => exact .direct (h.lift s n)
  | inverse h => exact .inverse (h.lift s n)
end Lamping.AG

namespace Lamping.AG
open Graph
theorem Traversal.cons {k kind p q a b} (h : Traversal k kind p q a b) (x : Level) :
    Traversal (1+k) kind p q (a.cons x) (b.cons x) := by
  simpa only [Context.cons_replace_one] using h.lift (Context.empty.cons x) 1
/-- Every passive operator's legal traversal commutes with a low fan branch. -/
def fanActionPaths (f : Op) (i k : Nat) (q : Aux f) (branch : Bool)
    (s a b : Context) (x : Level)
    (h : Traversal k (.op f) (.inl ()) (.inr q) a b) :
    LocalPath (Schema.fanAction f i (i+1+k) (by omega)).left (.inl branch) (.inr q)
      (s.replace i (a.cons x))
      (s.replace i (b.cons (if branch then .star x else .o x))) ×
    LocalPath (Schema.fanAction f i (i+1+k) (by omega)).right.net (.inl branch) (.inr q)
      (s.replace i (a.cons x))
      (s.replace i (b.cons (if branch then .star x else .o x))) := by
  have plain := (h.cons x).lift s i
  have tagged := (h.cons (if branch then .star x else .o x)).lift s i
  have tagA : Traversal i (.op .fan) (.inr branch) (.inl ())
      (s.replace i (a.cons x)) (s.replace i (a.cons (if branch then .star x else .o x))) := by
    cases branch
    · exact .direct (.fanO s a x)
    · exact .direct (.fanStar s a x)
  have tagB : Traversal i (.op .fan) (.inr branch) (.inl ())
      (s.replace i (b.cons x)) (s.replace i (b.cons (if branch then .star x else .o x))) := by
    cases branch
    · exact .direct (.fanO s b x)
    · exact .direct (.fanStar s b x)
  have hi : i+(1+k)=i+1+k := by omega
  rw [hi] at plain tagged
  refine ⟨leftRoutePath .fan f i (i+1+k) branch q _ _ _ tagA tagged, ?_⟩
  refine ⟨[.inr (.inl (.inl branch)), .inl ⟨.inl branch,.inr q⟩,
      .inl ⟨.inr q,.inl ()⟩], rfl, rfl, ?_⟩
  exact Labelling.cons
    (LabelledTurn.node (g:=fanRight f i (i+1+k)) (.inl branch) (.inl ()) (.inr q) plain)
    (.cons (LabelledTurn.node (g:=fanRight f i (i+1+k)) (.inr q) (.inr branch) (.inl ()) tagB)
      (.single _ _))
/-- Cro inserts a level below the passive operator, so its index drops by one on RHS. -/
def croActionPaths (f : Op) (i k : Nat) (q : Aux f) (s a b : Context)
    (h : Traversal k (.op f) (.inl ()) (.inr q) a b) :
    LocalPath (Schema.croAction f i (i+1+k) (by omega)).left (.inl ()) (.inr q)
      (s.replace i a) (s.replace i (b.cons .empty)) ×
    LocalPath (Schema.croAction f i (i+1+k) (by omega)).right.net (.inl ()) (.inr q)
      (s.replace i a) (s.replace i (b.cons .empty)) := by
  have plain := h.lift s i
  have shifted := (h.cons .empty).lift s i
  have hi : i+(1+k)=i+1+k := by omega
  rw [hi] at shifted
  refine ⟨leftRoutePath .cro f i (i+1+k) () q _ _ _ (.direct (.cro s a)) shifted, ?_⟩
  have hk : i+1+k-1=i+k := by omega
  change LocalPath (unaryRightCore .cro f (Bij.refl _) i (i+1+k-1)) _ _ _ _
  rw [hk]
  refine ⟨[.inr (.inl (.inl ())), .inl ⟨.inl (),.inr q⟩,
      .inl ⟨.inr q,.inl ()⟩], rfl, rfl, ?_⟩
  exact Labelling.cons
    (LabelledTurn.node (g:=unaryRightCore .cro f (Bij.refl _) i (i+k)) (.inl ()) (.inl ()) (.inr q) plain)
    (.cons (LabelledTurn.node (g:=unaryRightCore .cro f (Bij.refl _) i (i+k)) (.inr q) (.inr ()) (.inl ())
      (.direct (.cro s b))) (.single _ _))
end Lamping.AG
namespace Lamping.AG
open Graph
/-- Bra packs two levels: the passive operator has one more level on RHS. -/
def braActionPaths (f : Op) (i k : Nat) (q : Aux f) (s a b : Context) (x y : Level)
    (h : Traversal k (.op f) (.inl ()) (.inr q) a b) :
    LocalPath (Schema.braAction f i (i+1+k) (by omega)).left (.inl ()) (.inr q)
      (s.replace i ((a.cons x).cons y)) (s.replace i (b.cons (.pair x y))) ×
    LocalPath (Schema.braAction f i (i+1+k) (by omega)).right.net (.inl ()) (.inr q)
      (s.replace i ((a.cons x).cons y)) (s.replace i (b.cons (.pair x y))) := by
  have packed := (h.cons (.pair x y)).lift s i
  have plain := ((h.cons x).cons y).lift s i
  have hi : i+(1+k)=i+1+k := by omega
  rw [hi] at packed
  refine ⟨leftRoutePath .bra f i (i+1+k) () q _ _ _ (.direct (.bra s a x y)) packed, ?_⟩
  have hk : i+1+k+1=i+(1+(1+k)) := by omega
  change LocalPath (unaryRightCore .bra f (Bij.refl _) i (i+1+k+1)) _ _ _ _
  rw [hk]
  refine ⟨[.inr (.inl (.inl ())), .inl ⟨.inl (),.inr q⟩,
      .inl ⟨.inr q,.inl ()⟩], rfl, rfl, ?_⟩
  exact Labelling.cons
    (LabelledTurn.node (g:=unaryRightCore .bra f (Bij.refl _) i (i+(1+(1+k)))) (.inl ()) (.inl ()) (.inr q) plain)
    (.cons (LabelledTurn.node (g:=unaryRightCore .bra f (Bij.refl _) i (i+(1+(1+k)))) (.inr q) (.inr ()) (.inl ())
      (.direct (.bra s b x y))) (.single _ _))
end Lamping.AG
namespace Lamping.AG
open Graph
/-- The passive application's context→argument path does not cross the active edge.
It must be included separately from active→passive route families. -/
def passiveAppLeft (active : Op) (i j : Nat) (a : Context) :
    LocalPath (leftNet active .app i j) (.inr false) (.inr true) a a where
  edges := [.inr (.inl (.inr false)), .inl ⟨.inr (),appArg⟩]
  start := rfl
  finish := rfl
  labeling := .cons (LabelledTurn.node (g:=leftNet active .app i j) (.inr ()) appCtx appArg
    (.direct (.appArg a))) (.single _ _)
/-- Same path identity on the fan RHS, choosing a low marker explicitly. This is
existential relabeling, not preservation of every source labeling. -/
def fanActionPassiveApp (i k : Nat) (branch : Bool) (s a : Context) (x : Level) :
    LocalPath (Schema.fanAction .app i (i+1+k) (by omega)).right.net (.inr false) (.inr true)
      (s.replace i (a.cons (if branch then .star x else .o x)))
      (s.replace i (a.cons (if branch then .star x else .o x))) := by
  have ht : Traversal i (.op .fan) (.inr branch) (.inl ())
      (s.replace i (a.cons x)) (s.replace i (a.cons (if branch then .star x else .o x))) := by
    cases branch
    · exact .direct (.fanO s a x)
    · exact .direct (.fanStar s a x)
  refine ⟨[.inr (.inl (.inr false)), .inl ⟨.inr false,.inr branch⟩,
      .inl ⟨.inl branch,appArg⟩, .inl ⟨.inr true,.inl ()⟩], rfl, rfl, ?_⟩
  exact .cons (LabelledTurn.node (g:=fanRight .app i (i+1+k)) (.inr false) (.inl ()) (.inr branch) ht.reverse)
    (.cons (LabelledTurn.node (g:=fanRight .app i (i+1+k)) (.inl branch) appCtx appArg (.direct (.appArg _)))
      (.cons (LabelledTurn.node (g:=fanRight .app i (i+1+k)) (.inr true) (.inr branch) (.inl ()) ht) (.single _ _)))
def croActionPassiveApp (i k : Nat) (s a : Context) :
    LocalPath (Schema.croAction .app i (i+1+k) (by omega)).right.net (.inr false) (.inr true)
      (s.replace i (a.cons .empty)) (s.replace i (a.cons .empty)) := by
  change LocalPath (unaryRightCore .cro .app (Bij.refl _) i (i+1+k-1)) _ _ _ _
  refine ⟨[.inr (.inl (.inr false)), .inl ⟨.inr false,.inr ()⟩,
      .inl ⟨.inl (),appArg⟩, .inl ⟨.inr true,.inl ()⟩], rfl, rfl, ?_⟩
  exact .cons (LabelledTurn.node (g:=unaryRightCore .cro .app (Bij.refl _) i (i+1+k-1)) (.inr false) (.inl ()) (.inr ()) (.inverse (.cro s a)))
    (.cons (LabelledTurn.node (g:=unaryRightCore .cro .app (Bij.refl _) i (i+1+k-1)) (.inl ()) appCtx appArg (.direct (.appArg _)))
      (.cons (LabelledTurn.node (g:=unaryRightCore .cro .app (Bij.refl _) i (i+1+k-1)) (.inr true) (.inr ()) (.inl ()) (.direct (.cro s a))) (.single _ _)))
def braActionPassiveApp (i k : Nat) (s a : Context) (x y : Level) :
    LocalPath (Schema.braAction .app i (i+1+k) (by omega)).right.net (.inr false) (.inr true)
      (s.replace i (a.cons (.pair x y))) (s.replace i (a.cons (.pair x y))) := by
  change LocalPath (unaryRightCore .bra .app (Bij.refl _) i (i+1+k+1)) _ _ _ _
  refine ⟨[.inr (.inl (.inr false)), .inl ⟨.inr false,.inr ()⟩,
      .inl ⟨.inl (),appArg⟩, .inl ⟨.inr true,.inl ()⟩], rfl, rfl, ?_⟩
  exact .cons (LabelledTurn.node (g:=unaryRightCore .bra .app (Bij.refl _) i (i+1+k+1)) (.inr false) (.inl ()) (.inr ()) (.inverse (.bra s a x y)))
    (.cons (LabelledTurn.node (g:=unaryRightCore .bra .app (Bij.refl _) i (i+1+k+1)) (.inl ()) appCtx appArg (.direct (.appArg _)))
      (.cons (LabelledTurn.node (g:=unaryRightCore .bra .app (Bij.refl _) i (i+1+k+1)) (.inr true) (.inr ()) (.inl ()) (.direct (.bra s a x y))) (.single _ _)))
end Lamping.AG


namespace Lamping.AG
/-- A low fan principal can only carry a marked level. -/
def MarkedFanInput (i : Nat) : (k : Kind) → Port k → Context → Prop
  | .op .fan,.inl _,a => a.get i ≠ .empty
  | _,_,_ => True
theorem Passage.incoming_marked {i k p q a b} (h : Passage i k p q a b) :
    MarkedFanInput i k p a := by
  cases h <;> simp [AG.fanO,AG.fanStar,MarkedFanInput]
theorem Passage.outgoing_marked {i k p q a b} (h : Passage i k p q a b) :
    MarkedFanInput i k q b := by
  cases h <;> simp [MarkedFanInput,Context.replace,Context.cons]
theorem Traversal.incoming_marked {i k p q a b} (h : Traversal i k p q a b) :
    MarkedFanInput i k p a := by
  cases h with
  | direct h => exact h.incoming_marked
  | inverse h => exact h.outgoing_marked
theorem no_empty_fan_exit (branch : Bool) (b : Context) :
    ¬Traversal 0 (.op .fan) (.inl ()) (.inr branch) Context.empty b := by
  intro h; exact h.incoming_marked rfl
end Lamping.AG

namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
def MarkedAtEnd : Endpoint g → Context → Prop
  | .inl ⟨n,p⟩,a => MarkedFanInput (g.label n).index (g.label n).sort p a
  | _,_ => True
theorem LabelledTurn.incoming_marked {e f a b} (h : LabelledTurn g e f a b) : MarkedAtEnd g e a := by
  cases h with
  | node n p q h => exact h.incoming_marked
  | transparent => trivial
theorem Labelling.first_marked {e f es a b} (h : Labelling g (e::f::es) a b) :
    MarkedAtEnd g (g.wire e) a := by
  cases h with | cons h _ => exact h.incoming_marked
end
/-- Actual rule-Net counterexample to preservation of every source labeling. The
passive application ctx→arg exists on LHS with empty context, but not on RHS. -/
theorem no_empty_fanAction_passiveApp (i : Nat) (lt : 0<i) :
    ¬Nonempty (LocalPath (Schema.fanAction .app 0 i lt).right.net (.inr false) (.inr true)
      Context.empty Context.empty) := by
  rintro ⟨p⟩
  cases he : p.edges with
  | nil => have hs := p.start; simp [he] at hs
  | cons e es =>
    have hs := p.start
    rw [he] at hs
    simp only [List.head?_cons,Option.some.injEq] at hs
    subst e
    cases es with
    | nil =>
      have hf := p.finish
      rw [he] at hf
      simp [Schema.right,fanRight] at hf
    | cons f es =>
      have hm := Labelling.first_marked (g:=fanRight .app 0 i) (by rw [←he]; exact p.labeling)
      exact hm rfl
end Lamping.AG


namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem Labelling.append_turn {es : List (Endpoint g)} {e f : Endpoint g}
    (h : Labelling g es a b) (last : es.getLast?=some e)
    (turn : LabelledTurn g (g.wire e) f b c) : Labelling g (es++[f]) a c := by
  induction h with
  | single x a =>
    simp only [List.getLast?_cons,List.getLast?_nil,Option.some.injEq] at last
    subst e; exact .cons turn (.single _ _)
  | cons ht hs ih =>
    apply Labelling.cons ht
    exact ih (by simpa using last) turn
/-- Reversing a path reverses occurrences; it does not erase repeated segments. -/
def reverseEdges (es : List (Endpoint g)) : List (Endpoint g) := es.reverse.map g.wire.mate
theorem Labelling.reverse {es : List (Endpoint g)} (h : Labelling g es a b) :
    Labelling g (reverseEdges es) b a := by
  induction h with
  | single e a => exact .single _ _
  | @cons e f es a b c ht hs ih =>
    rw [show reverseEdges (e::f::es) = reverseEdges (f::es) ++ [g.wire e] from by simp [reverseEdges]]
    apply ih.append_turn (e:=g.wire f)
    · simp [reverseEdges]
    · simpa only [Pairing.involutive] using ht.reverse
/-- The local route interface is closed under reversing real segment occurrences. -/
def LocalPath.reverse {x y : B} {a b : Context} (p : LocalPath g x y a b) : LocalPath g y x b a where
  edges := reverseEdges p.edges
  start := by simpa [reverseEdges,Pairing.involutive] using congrArg (Option.map g.wire.mate) p.finish
  finish := by simpa [reverseEdges] using congrArg (Option.map g.wire.mate) p.start
  labeling := p.labeling.reverse
end
end Lamping.AG


namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- A genuine transparent wire route is labelable by every constant context. -/
theorem transparent_labeling (es : List (Endpoint g)) (nonempty : es≠[])
    (transparent : ∀ e f, (e,f) ∈ es.zip es.tail →
      ∃ w d, g.wire e=.inr (.inr (w,d)) ∧ f=.inr (.inr (w,!d))) (a : Context) :
    Labelling g es a a := by
  induction es with
  | nil => exact False.elim (nonempty rfl)
  | cons e es ih =>
    cases es with
    | nil => exact .single e a
    | cons f es =>
      obtain ⟨w,d,he,hf⟩ := transparent e f (by simp)
      refine .cons ?_ (ih (by simp) ?_)
      · rw [he,hf]; exact .transparent w d a
      · intro x y h; exact transparent x y (by simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr h)
theorem transparent_forward (es : List (Endpoint g)) (nonempty : es≠[])
    (transparent : ∀ e f, (e,f) ∈ es.zip es.tail →
      ∃ w d, g.wire e=.inr (.inr (w,d)) ∧ f=.inr (.inr (w,!d))) :
    Forward g es := by
  induction es with
  | nil => exact False.elim (nonempty rfl)
  | cons e es ih =>
    cases es with
    | nil => exact .single e
    | cons f es =>
      obtain ⟨w,d,he,hf⟩ := transparent e f (by simp)
      apply Forward.transparent w d he hf
      exact ih (by simp) (by intro x y h; exact transparent x y (by simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr h))
theorem BetaEdge.principal_nonempty (r : BetaEdge g) : r.principal≠[] := by
  intro h; have hs:=r.principalStart; simp [h] at hs
theorem BetaEdge.principal_labeling (r : BetaEdge g) (a : Context) :
    Labelling g r.principal a a := transparent_labeling _ r.principal_nonempty r.transparent a
theorem BetaEdge.principal_forward (r : BetaEdge g) : Forward g r.principal :=
  transparent_forward _ r.principal_nonempty r.transparent
theorem BetaEdge.reverse_labeling (r : BetaEdge g) (a : Context) :
    Labelling g r.reverseRoute a a := (r.principal_labeling a).reverse
theorem BetaEdge.reverse_start (r : BetaEdge g) : r.reverseRoute.head?=some r.ctxEnd := by
  simpa [BetaEdge.reverseRoute,BetaEdge.ctxEnd,Pairing.involutive] using
    congrArg (Option.map g.wire.mate) r.principalEnd
theorem BetaEdge.reverse_finish (r : BetaEdge g) : r.reverseRoute.getLast?=some (g.wire r.funEnd) := by
  simpa [BetaEdge.reverseRoute,BetaEdge.funEnd] using congrArg (Option.map g.wire.mate) r.principalStart
end
end Lamping.AG
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- Concatenate nonoverlapping expanded pieces at their actual endpoint turn. -/
theorem ExpandedLabelling.splice {es fs : List (Endpoint g)} {e f : Endpoint g}
    (h : ExpandedLabelling g es a b) (last : es.getLast?=some e)
    (k : ExpandedLabelling g fs c d) (first : fs.head?=some f)
    (turn : ExpandedTurn g (g.wire e) f b c) : ExpandedLabelling g (es++fs) a d := by
  induction h with
  | single x a =>
    simp only [List.getLast?_cons,List.getLast?_nil,Option.some.injEq] at last
    subst e
    cases fs with
    | nil => simp at first
    | cons y ys => simp only [List.head?_cons,Option.some.injEq] at first; subst f; exact .cons turn k
  | cons ht hs ih =>
    exact .cons ht (ih (by simpa using last) turn)
/-- Local beta-backward surgery on a labelled (possibly expanded) body→binding
loop. No endpoint-context equality is assumed: the reverse beta route carries the
loop's final context, as required by PDF74. -/
theorem BetaEdge.expand_loop_labeling (r : BetaEdge g) {loop : List (Endpoint g)}
    (h : ExpandedLabelling g loop a b)
    (ends : loop.getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩))) :
    ExpandedLabelling g (loop ++ r.reverseRoute ++ [r.argEnd]) a b := by
  have reverseLabels : ExpandedLabelling g r.reverseRoute b b := (r.reverse_labeling b).expanded
  have bodyThenReverse : ExpandedLabelling g (loop++r.reverseRoute) a b := by
    apply h.splice ends reverseLabels r.reverse_start
    simpa only [Pairing.involutive] using ExpandedTurn.bindToCtx (g:=g) r b
  have hend : (loop++r.reverseRoute).getLast?=some (g.wire r.funEnd) := by
    simp only [List.getLast?_append,r.reverse_finish,Option.some_or]
  apply bodyThenReverse.splice hend (ExpandedLabelling.single r.argEnd b) rfl
  simpa only [Pairing.involutive] using ExpandedTurn.funToArg (g:=g) r b
end
end Lamping.AG
namespace Lamping.AG
/-- Observable branch constraint at a fan, valid for either crossing direction. -/
def FanEdgeMarker (i : Nat) : (k : Kind) → Port k → Port k → Context → Context → Prop
  | .op .fan,.inr branch,.inl _,a,b =>
      b.get i = if branch=true then Level.star (a.get i) else Level.o (a.get i)
  | .op .fan,.inl _,.inr branch,a,b =>
      a.get i = if branch=true then Level.star (b.get i) else Level.o (b.get i)
  | _,_,_,_,_ => True
theorem Traversal.fan_marker {i k p q a b} (h : Traversal i k p q a b) :
    FanEdgeMarker i k p q a b := by
  cases h with
  | direct h => cases h <;> simp [AG.fanO,AG.fanStar,FanEdgeMarker,Context.replace,Context.cons]
  | inverse h => cases h <;> simp [AG.fanO,AG.fanStar,FanEdgeMarker,Context.replace,Context.cons]
/-- Fan cancellation cannot cross from o to star, even when contexts are existential. -/
theorem fan_cancel_same_branch (i : Nat) (left right : Bool) (a mid b : Context)
    (h : Traversal i (.op .fan) (.inr left) (.inl ()) a mid)
    (k : Traversal i (.op .fan) (.inl ()) (.inr right) mid b) : left=right := by
  have hm := h.fan_marker
  have hk := k.fan_marker
  change mid.get i=(if left then .star (a.get i) else .o (a.get i)) at hm
  change mid.get i=(if right then .star (b.get i) else .o (b.get i)) at hk
  cases left <;> cases right <;> simp_all
end Lamping.AG

namespace Lamping.AG
open Graph
/-- All control auxiliary entrances lead to their principal port. -/
def ControlAuxOutput : (k : Kind) → Port k → Port k → Prop
  | .op .fan,.inr _,q => q=Sum.inl ()
  | .op .cro,.inr _,q => q=Sum.inl ()
  | .op .bra,.inr _,q => q=Sum.inl ()
  | _,_,_ => True
theorem Traversal.control_aux {i k p q a b} (h : Traversal i k p q a b) : ControlAuxOutput k p q := by
  cases h with
  | direct h => cases h <;> simp [AG.fanO,AG.fanStar,ControlAuxOutput]
  | inverse h => cases h <;> simp [ControlAuxOutput]
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- Invert an actual labelled turn at a specified node occurrence. -/
theorem LabelledTurn.from_node {e f : Endpoint g} {a b : Context}
    (h : LabelledTurn g e f a b) (n : N) (p : Port (g.label n).sort)
    (atNode : e=.inl ⟨n,p⟩) :
    ∃ q, f=.inl ⟨n,q⟩ ∧ Traversal (g.label n).index (g.label n).sort p q a b := by
  cases h with
  | node n' p' q' rule => cases atNode; exact ⟨q',rfl,rule⟩
  | transparent w d a => cases atNode
theorem LabelledTurn.not_boundary {e f : Endpoint g} {a b : Context}
    (h : LabelledTurn g e f a b) (boundary : B) : e≠.inr (.inl boundary) := by
  cases h <;> intro eq <;> cases eq
end
end Lamping.AG
namespace Lamping.AG
open Graph
/-- Inversion of every labeling on the actual principal-crossing route. The source
relations are extracted from graph incidence, not supplied as target correctness. -/
theorem leftRoute_labeling_iff (f h : Op) (i j : Nat) (x : Aux f) (y : Aux h) (a c : Context) :
    Labelling (leftNet f h i j) (leftRoute f h i j x y) a c ↔
      ∃ b, Traversal i (.op f) (.inr x) (.inl ()) a b ∧
        Traversal j (.op h) (.inl ()) (.inr y) b c := by
  constructor
  · intro path
    cases path with
    | cons first rest =>
      obtain ⟨p,hp,hfirst⟩ := first.from_node (.inl ()) (.inr x) rfl
      have hp' : p=Sum.inl () := by
        have := sigma_snd_heq (Sum.inl.inj hp)
        exact (eq_of_heq this).symm
      subst p
      cases rest with
      | cons second last =>
        cases last
        obtain ⟨q,hq,hsecond⟩ := second.from_node (.inr ()) (.inl ()) rfl
        have hq' : q=Sum.inr y := by
          have := sigma_snd_heq (Sum.inl.inj hq)
          exact (eq_of_heq this).symm
        subst q
        exact ⟨_,hfirst,hsecond⟩
  · rintro ⟨b,first,second⟩
    exact (leftRoutePath f h i j x y a b c first second).labeling
end Lamping.AG
namespace Lamping.AG.Context
theorem replace_cons_other (s a : Context) (i t : Nat) (x y : Level) (ne : t≠i) :
    (s.replace i (a.cons x)).get t = (s.replace i (a.cons y)).get t := by
  by_cases low : t<i
  · simp [replace,low]
  · have positive : 0<t-i := by omega
    cases diff : t-i with
    | zero => omega
    | succ k => simp [replace,low,diff]
end Lamping.AG.Context
namespace Lamping.AG
def FanOtherLevels (i : Nat) : Kind → Context → Context → Prop
  | .op .fan,a,b => ∀ t, t≠i → a.get t=b.get t
  | _,_,_ => True
theorem Traversal.fan_other_levels {i k p q a b} (h : Traversal i k p q a b) :
    FanOtherLevels i k a b := by
  cases h with
  | direct h =>
    cases h <;> simp only [FanOtherLevels]
    · intro t ne; exact Context.replace_cons_other _ _ _ _ _ _ ne
    · intro t ne; exact Context.replace_cons_other _ _ _ _ _ _ ne
    all_goals trivial
  | inverse h =>
    cases h <;> simp only [FanOtherLevels]
    · intro t ne; exact Context.replace_cons_other _ _ _ _ _ _ ne
    · intro t ne; exact Context.replace_cons_other _ _ _ _ _ _ ne
    all_goals trivial
theorem fan_cancel_context (i : Nat) (left right : Bool) (a mid b : Context)
    (h : Traversal i (.op .fan) (.inr left) (.inl ()) a mid)
    (k : Traversal i (.op .fan) (.inl ()) (.inr right) mid b) : a=b := by
  have branch := fan_cancel_same_branch i left right a mid b h k
  subst right
  apply Context.ext
  intro t
  by_cases eq : t=i
  · subst t
    have hm := h.fan_marker
    have hk := k.fan_marker
    cases left <;> simp_all [FanEdgeMarker]
  · exact (h.fan_other_levels t eq).trans (k.fan_other_levels t eq)
end Lamping.AG
namespace Lamping.AG
/-- Transport of every proper labeling of a fan-cancellation principal route,
including proof that its branches and full endpoint contexts must agree. -/
theorem fanCancel_route_transport (i : Nat) (left right : Bool) (a b : Context)
    (h : Labelling (Schema.fanCancel i).left (leftRoute .fan .fan i i left right) a b) :
    Nonempty (LocalPath (Schema.fanCancel i).right.net (.inl left) (.inr right) a b) := by
  obtain ⟨mid,hleft,hright⟩ := (leftRoute_labeling_iff .fan .fan i i left right a b).mp h
  have branch := fan_cancel_same_branch i left right a mid b hleft hright
  have same := fan_cancel_context i left right a mid b hleft hright
  subst right; subst b
  exact ⟨fanCancelRight i left a⟩
end Lamping.AG


namespace Lamping.AG
/-- Recover the pre-Cro context by deleting the inserted level. -/
def CroRecover (i : Nat) (a b : Context) : Prop :=
  ∀ t, a.get t = if t<i then b.get t else b.get (t+1)
def CroEdgeConstraint (i : Nat) : (k : Kind) → Port k → Port k → Context → Context → Prop
  | .op .cro,.inr _,.inl _,a,b => CroRecover i a b
  | .op .cro,.inl _,.inr _,a,b => CroRecover i b a
  | _,_,_,_,_ => True
theorem cro_recover_insert (s a : Context) (i : Nat) :
    CroRecover i (s.replace i a) (s.replace i (a.cons .empty)) := by
  intro t
  by_cases low : t<i
  · simp [low,Context.replace]
  · simp [low,Context.replace,show ¬t+1<i by omega,show t+1-i=(t-i)+1 by omega]
theorem Traversal.cro_constraint {i k p q a b} (h : Traversal i k p q a b) :
    CroEdgeConstraint i k p q a b := by
  cases h with
  | direct h =>
    cases h <;> simp only [CroEdgeConstraint]
    case cro s t => exact cro_recover_insert s t i
    all_goals trivial
  | inverse h =>
    cases h <;> simp only [CroEdgeConstraint]
    case cro s t => exact cro_recover_insert s t i
    all_goals trivial
theorem cro_cancel_context (i : Nat) (a mid b : Context)
    (h : Traversal i (.op .cro) (.inr ()) (.inl ()) a mid)
    (k : Traversal i (.op .cro) (.inl ()) (.inr ()) mid b) : a=b := by
  ext t
  exact (h.cro_constraint t).trans (k.cro_constraint t).symm
theorem croCancel_route_transport (i : Nat) (a b : Context)
    (h : Labelling (Schema.croCancel i).left (leftRoute .cro .cro i i () ()) a b) :
    Nonempty (LocalPath (Schema.croCancel i).right.net (.inl ()) (.inr ()) a b) := by
  obtain ⟨mid,hleft,hright⟩ := (leftRoute_labeling_iff .cro .cro i i () () a b).mp h
  have same := cro_cancel_context i a mid b hleft hright
  subst b; exact ⟨croCancelRight i a⟩
end Lamping.AG
namespace Lamping.AG
namespace Level
def pairLeft : Level → Level | .pair a _ => a | _ => .empty
def pairRight : Level → Level | .pair _ b => b | _ => .empty
end Level
/-- Recover the two levels packed by a Bra; this is not the Cro shift operation. -/
def BraRecover (i : Nat) (a b : Context) : Prop := ∀ t, a.get t =
  if t<i then b.get t else if t=i then (b.get i).pairRight
  else if t=i+1 then (b.get i).pairLeft else b.get (t-1)
def BraEdgeConstraint (i : Nat) : (k : Kind) → Port k → Port k → Context → Context → Prop
  | .op .bra,.inr _,.inl _,a,b => BraRecover i a b
  | .op .bra,.inl _,.inr _,a,b => BraRecover i b a
  | _,_,_,_,_ => True
theorem bra_recover_pack (s a : Context) (i : Nat) (x y : Level) :
    BraRecover i (s.replace i ((a.cons x).cons y)) (s.replace i (a.cons (.pair x y))) := by
  intro t
  by_cases low : t<i
  · simp [low,Context.replace]
  · by_cases equal : t=i
    · subst t; simp [Context.replace,Context.cons,Level.pairRight]
    · by_cases next : t=i+1
      · subst t; simp [Context.replace,Context.cons,Level.pairLeft,show ¬i+1<i by omega]
      · have pos : i+1<t := by omega
        have d1 : t-i=(t-i-2)+1+1 := by omega
        have d2 : t-1-i=(t-i-2)+1 := by omega
        simp only [if_neg low,if_neg equal,if_neg next]
        rw [Context.replace_high _ _ (by omega),Context.replace_high _ _ (by omega),d1,d2]
        rfl
theorem Traversal.bra_constraint {i k p q a b} (h : Traversal i k p q a b) :
    BraEdgeConstraint i k p q a b := by
  cases h with
  | direct h =>
    cases h <;> simp only [BraEdgeConstraint]
    case bra s t x y => exact bra_recover_pack s t i x y
    all_goals trivial
  | inverse h =>
    cases h <;> simp only [BraEdgeConstraint]
    case bra s t x y => exact bra_recover_pack s t i x y
    all_goals trivial
theorem bra_cancel_context (i : Nat) (a mid b : Context)
    (h : Traversal i (.op .bra) (.inr ()) (.inl ()) a mid)
    (k : Traversal i (.op .bra) (.inl ()) (.inr ()) mid b) : a=b := by
  ext t
  exact (h.bra_constraint t).trans (k.bra_constraint t).symm
theorem braCancel_route_transport (i : Nat) (a b : Context)
    (h : Labelling (Schema.braCancel i).left (leftRoute .bra .bra i i () ()) a b) :
    Nonempty (LocalPath (Schema.braCancel i).right.net (.inl ()) (.inr ()) a b) := by
  obtain ⟨mid,hleft,hright⟩ := (leftRoute_labeling_iff .bra .bra i i () () a b).mp h
  have same := bra_cancel_context i a mid b hleft hright
  subst b; exact ⟨braCancelRight i a⟩
end Lamping.AG

namespace Lamping.AG
open Graph
/-- Exhaustiveness of actual boundary-to-boundary paths entering the active control.
No finite/simple-path assumption is used; the graph incidence and forbidden turns
force precisely the three principal-crossing segments. -/
theorem left_control_route_shape (f h : Op) (control : f=.fan ∨ f=.cro ∨ f=.bra)
    (i j : Nat) (x : Aux f) (y : Aux h) (es : List (Endpoint (leftNet f h i j)))
    (a c : Context)
    (path : Labelling (leftNet f h i j) (.inr (.inl (.inl x))::es) a c)
    (last : (.inr (.inl (.inl x))::es).getLast?=some (.inl ⟨.inr (),.inr y⟩)) :
    (.inr (.inl (.inl x))::es)=leftRoute f h i j x y := by
  cases es with
  | nil => simp at last
  | cons e es =>
    cases path with
    | cons first rest =>
      obtain ⟨q,hq,hfirst⟩ := first.from_node (.inl ()) (.inr x) rfl
      have principal : q=Sum.inl () := by
        rcases control with eq | eq | eq
        · subst f; exact hfirst.control_aux
        · subst f; exact hfirst.control_aux
        · subst f; exact hfirst.control_aux
      subst q; subst e
      cases es with
      | nil => simp at last
      | cons e es =>
        cases rest with
        | cons second tail =>
          obtain ⟨q,hq,hsecond⟩ := second.from_node (.inr ()) (.inl ()) rfl
          cases q with
          | inl u => cases u; exact False.elim (hsecond.distinct rfl)
          | inr z =>
            subst e
            cases es with
            | nil =>
              have eq : z=y := by
                have pairEq : (Sigma.mk (Sum.inr ()) (Sum.inr z) : NodePort signature (Unit ⊕ Unit) (leftNet f h i j).label)=⟨.inr (),.inr y⟩ := by
                  simpa using last
                have hh : HEq (Sum.inr z : Port (.op h)) (Sum.inr y : Port (.op h)) := sigma_snd_heq pairEq
                have he := eq_of_heq hh
                exact Sum.inr.inj he
              subst z; rfl
            | cons e es =>
              cases tail with
              | cons third _ => exact False.elim (third.not_boundary (.inr z) rfl)
end Lamping.AG

namespace Lamping.AG
/-- The only auxiliary-to-auxiliary proper passage is application context↔argument. -/
def AuxAuxConstraint : (k : Kind) → Port k → Port k → Context → Context → Prop
  | .op .app,.inr x,.inr y,a,b =>
      ((x=false ∧ y=true) ∨ (x=true ∧ y=false)) ∧ a=b
  | .op _,.inr _,.inr _,_,_ => False
  | _,_,_,_,_ => True
theorem Traversal.aux_aux {i k p q a b} (h : Traversal i k p q a b) :
    AuxAuxConstraint k p q a b := by
  cases h with
  | direct h => cases h <;> simp [AG.appCtx,AG.appArg,AG.fanO,AG.fanStar,AuxAuxConstraint]
  | inverse h => cases h <;> simp [AG.appCtx,AG.appArg,AG.lamBody,AuxAuxConstraint]
end Lamping.AG
namespace Lamping.AG
/-- Reindex a legal local passage existentially. Contexts are re-chosen, not assumed
unchanged; this is useful precisely for local path identity transport. -/
theorem Passage.reindex {i k p q a b} (h : Passage i k p q a b) (j : Nat) :
    ∃ x y, Passage j k p q x y := by
  cases h with
  | fanO => exact ⟨_,_,.fanO Context.empty Context.empty .empty⟩
  | fanStar => exact ⟨_,_,.fanStar Context.empty Context.empty .empty⟩
  | cro => exact ⟨_,_,.cro Context.empty Context.empty⟩
  | bra => exact ⟨_,_,.bra Context.empty Context.empty .empty .empty⟩
  | appFun => exact ⟨_,_,.appFun Context.empty⟩
  | appArg => exact ⟨_,_,.appArg Context.empty⟩
  | lamBody => exact ⟨_,_,.lamBody Context.empty⟩
theorem Traversal.reindex {i k p q a b} (h : Traversal i k p q a b) (j : Nat) :
    ∃ x y, Traversal j k p q x y := by
  cases h with
  | direct h => obtain ⟨x,y,hh⟩ := h.reindex j; exact ⟨x,y,.direct hh⟩
  | inverse h => obtain ⟨x,y,hh⟩ := h.reindex j; exact ⟨y,x,.inverse hh⟩
theorem Passage.low {i k p q a b} (h : Passage i k p q a b) : Context.SameShell i a b := by
  intro t ht
  cases h <;> simp [Context.replace,ht]
theorem Traversal.low {i k p q a b} (h : Traversal i k p q a b) : Context.SameShell i a b := by
  cases h with
  | direct h => exact h.low
  | inverse h => intro t ht; exact (h.low t ht).symm
end Lamping.AG
namespace Lamping.AG
/-- Precise local target: preserve the old low shell, while existentially choosing
higher labels. This does not assert that these labels glue to the old exterior. -/
def ShellRelabel {N B W : Type} [Graph.FiniteNames N] [Graph.FiniteNames B] [Graph.FiniteNames W]
    (g : Graph.Net signature N B W) (x y : B) (i : Nat) (a b : Context) : Prop :=
  ∃ a' b', Context.SameShell i a a' ∧ Context.SameShell i b b' ∧ Nonempty (LocalPath g x y a' b')
theorem fanAction_cross_relabel (f : Op) (i j : Nat) (lt : i<j) (branch : Bool) (q : Aux f)
    (a b : Context)
    (path : Labelling (Schema.fanAction f i j lt).left (leftRoute .fan f i j branch q) a b) :
    ShellRelabel (Schema.fanAction f i j lt).right.net (.inl branch) (.inr q) i a b := by
  obtain ⟨gap, rfl⟩ : ∃ gap, j=i+1+gap := ⟨j-i-1,by omega⟩
  obtain ⟨mid,first,second⟩ := (leftRoute_labeling_iff .fan f i (i+1+gap) branch q a b).mp path
  have oldShell : Context.SameShell i a b := by
    intro t ht; exact (first.low t ht).trans (second.low t (by omega))
  obtain ⟨c,d,passive⟩ := second.reindex gap
  have route := (fanActionPaths f i gap q branch a c d .empty passive).2
  refine ⟨_,_,Context.sameShell_replace a _ i,?_,⟨route⟩⟩
  intro t ht
  exact (oldShell t ht).symm.trans (Context.sameShell_replace a _ i t ht)
theorem croAction_cross_relabel (f : Op) (i j : Nat) (lt : i<j) (q : Aux f)
    (a b : Context)
    (path : Labelling (Schema.croAction f i j lt).left (leftRoute .cro f i j () q) a b) :
    ShellRelabel (Schema.croAction f i j lt).right.net (.inl ()) (.inr q) i a b := by
  obtain ⟨gap, rfl⟩ : ∃ gap, j=i+1+gap := ⟨j-i-1,by omega⟩
  obtain ⟨mid,first,second⟩ := (leftRoute_labeling_iff .cro f i (i+1+gap) () q a b).mp path
  have oldShell : Context.SameShell i a b := by
    intro t ht; exact (first.low t ht).trans (second.low t (by omega))
  obtain ⟨c,d,passive⟩ := second.reindex gap
  have route := (croActionPaths f i gap q a c d passive).2
  refine ⟨_,_,Context.sameShell_replace a _ i,?_,⟨route⟩⟩
  intro t ht
  exact (oldShell t ht).symm.trans (Context.sameShell_replace a _ i t ht)
theorem braAction_cross_relabel (f : Op) (i j : Nat) (lt : i<j) (q : Aux f)
    (a b : Context)
    (path : Labelling (Schema.braAction f i j lt).left (leftRoute .bra f i j () q) a b) :
    ShellRelabel (Schema.braAction f i j lt).right.net (.inl ()) (.inr q) i a b := by
  obtain ⟨gap, rfl⟩ : ∃ gap, j=i+1+gap := ⟨j-i-1,by omega⟩
  obtain ⟨mid,first,second⟩ := (leftRoute_labeling_iff .bra f i (i+1+gap) () q a b).mp path
  have oldShell : Context.SameShell i a b := by
    intro t ht; exact (first.low t ht).trans (second.low t (by omega))
  obtain ⟨c,d,passive⟩ := second.reindex gap
  have route := (braActionPaths f i gap q a c d .empty .empty passive).2
  refine ⟨_,_,Context.sameShell_replace a _ i,?_,⟨route⟩⟩
  intro t ht
  exact (oldShell t ht).symm.trans (Context.sameShell_replace a _ i t ht)
end Lamping.AG



namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem Forward.append_transparent {es : List (Endpoint g)} {e f : Endpoint g}
    (h : Forward g es) (last : es.getLast?=some e) (w : W) (d : Bool)
    (arrives : g.wire e=.inr (.inr (w,d))) (leaves : f=.inr (.inr (w,!d))) :
    Forward g (es++[f]) := by
  induction h with
  | single x =>
    simp only [List.getLast?_cons,List.getLast?_nil,Option.some.injEq] at last
    subst e; exact .transparent w d arrives leaves (.single f)
  | node n p q ha hl hd hs ih =>
    exact .node n p q ha hl hd (ih (by simpa using last))
  | transparent v z ha hl hs ih =>
    exact .transparent v z ha hl (ih (by simpa using last))
theorem transparent_reverse_forward (es : List (Endpoint g)) (nonempty : es≠[])
    (transparent : ∀ e f, (e,f) ∈ es.zip es.tail →
      ∃ w d, g.wire e=.inr (.inr (w,d)) ∧ f=.inr (.inr (w,!d))) :
    Forward g (reverseEdges es) := by
  induction es with
  | nil => exact False.elim (nonempty rfl)
  | cons e es ih =>
    cases es with
    | nil => exact .single _
    | cons f es =>
      obtain ⟨w,d,he,hf⟩ := transparent e f (by simp)
      have tail := ih (by simp) (by intro x y h; exact transparent x y (by simp only [List.tail_cons,List.zip_cons_cons,List.mem_cons]; exact Or.inr h))
      rw [show reverseEdges (e::f::es)=reverseEdges (f::es)++[g.wire e] from by simp [reverseEdges]]
      apply tail.append_transparent (e:=g.wire f) (w:=w) (d:=!d)
      · simp [reverseEdges]
      · simpa only [Pairing.involutive] using hf
      · simpa using he
theorem BetaEdge.reverse_forward (r : BetaEdge g) : Forward g r.reverseRoute :=
  transparent_reverse_forward _ r.principal_nonempty r.transparent
end
end Lamping.AG
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem ExpandedForward.splice {es fs : List (Endpoint g)} {e f : Endpoint g}
    (h : ExpandedForward g es) (last : es.getLast?=some e)
    (k : ExpandedForward g fs) (first : fs.head?=some f)
    (turn : ExpandedDirection g (g.wire e) f) : ExpandedForward g (es++fs) := by
  induction h with
  | single x =>
    simp only [List.getLast?_cons,List.getLast?_nil,Option.some.injEq] at last
    subst e
    cases fs with
    | nil => simp at first
    | cons y ys => simp only [List.head?_cons,Option.some.injEq] at first; subst f; exact .cons turn k
  | cons ht hs ih => exact .cons ht (ih (by simpa using last))
theorem ExpandedForward.of_append {pre es : List (Endpoint g)} (h : ExpandedForward g (pre++es))
    (nonempty : es≠[]) : ExpandedForward g es := by
  induction pre with
  | nil => exact h
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases es with
      | nil => exact False.elim (nonempty rfl)
      | cons y ys => cases h with | cons _ hs => exact hs
    | cons y ys => cases h with | cons _ hs => exact ih hs
/-- Every minimally generated expanded proper path really obeys the expanded
forward grammar on the actual Net, even when the principal wire is subdivided. -/
theorem ExpandedProperPath.forward {root es} (h : ExpandedProperPath g root es) :
    ExpandedForward g es := by
  induction h with
  | base path _ => exact path.2.expanded
  | insert r pre loop suffix _ _ _ _ loopEnd _ _ _ _ argIH bodyIH =>
    have arg := argIH.of_append (by simp : r.argEnd::suffix≠[])
    have rev := r.reverse_forward.expanded
    have bodyEnd : (pre++r.principal++loop).getLast?=some (g.wire (.inl ⟨r.lam,r.lamBind⟩)) := by
      simp only [List.getLast?_append,loopEnd,Option.some_or]
    have first : ExpandedForward g ((pre++r.principal++loop)++r.reverseRoute) := by
      apply bodyIH.splice bodyEnd rev r.reverse_start
      simpa only [Pairing.involutive] using ExpandedDirection.bindToCtx (g:=g) r
    have firstEnd : ((pre++r.principal++loop)++r.reverseRoute).getLast?=some (g.wire r.funEnd) := by
      simp only [List.getLast?_append,r.reverse_finish,Option.some_or]
    have final := first.splice firstEnd arg rfl (by simpa only [Pairing.involutive] using ExpandedDirection.funToArg (g:=g) r)
    simpa only [List.append_assoc,List.singleton_append] using final
end
end Lamping.AG

namespace Lamping.AG
/-- Proper-node passages never change contexts. -/
def ProperContextInvariant : Kind → Context → Context → Prop
  | .op .app,a,b | .op .lam,a,b => a=b
  | _,_,_ => True
theorem Traversal.proper_context {i k p q a b} (h : Traversal i k p q a b) :
    ProperContextInvariant k a b := by
  cases h with
  | direct h => cases h <;> simp [ProperContextInvariant]
  | inverse h => cases h <;> simp [ProperContextInvariant]
/-- Beta's context→body route transports every labeling, not just one witness. -/
theorem beta_context_body_transport (i : Nat) (a b : Context)
    (h : Labelling (Schema.beta i).left (leftRoute .app .lam i i false true) a b) :
    Nonempty (LocalPath (Schema.beta i).right.net (.inl false) (.inr true) a b) := by
  obtain ⟨mid,first,second⟩ := (leftRoute_labeling_iff .app .lam i i false true a b).mp h
  have one : a=mid := first.proper_context
  have two : mid=b := second.proper_context
  cases one; cases two; exact ⟨betaRight i a⟩
/-- The other beta reconnection is binding→argument, and has the same context. -/
def beta_binding_argument_right (i : Nat) (a : Context) :
    LocalPath (Schema.beta i).right.net (.inr false) (.inl true) a a :=
  (wirePath boolFlip true a).reverse
end Lamping.AG

namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- A local expanded beta passage starts with the incoming binding segment,
retains every reversed principal segment, and exits through the argument. -/
def BetaEdge.backwardPiece (r : BetaEdge g) : List (Endpoint g) :=
  [g.wire (.inl ⟨r.lam,r.lamBind⟩)] ++ r.reverseRoute ++ [r.argEnd]
theorem BetaEdge.backward_piece_labeling (r : BetaEdge g) (a : Context) :
    ExpandedLabelling g r.backwardPiece a a :=
  r.expand_loop_labeling (.single _ a) rfl
theorem BetaEdge.backward_piece_forward (r : BetaEdge g) : ExpandedForward g r.backwardPiece := by
  have rlabels := r.reverse_forward.expanded
  have one : ExpandedForward g ([g.wire (.inl ⟨r.lam,r.lamBind⟩)]++r.reverseRoute) := by
    apply (ExpandedForward.single (g:=g) (g.wire (.inl ⟨r.lam,r.lamBind⟩))).splice (e:=g.wire (.inl ⟨r.lam,r.lamBind⟩)) rfl rlabels r.reverse_start
    simpa only [Pairing.involutive] using ExpandedDirection.bindToCtx (g:=g) r
  have last : ([g.wire (.inl ⟨r.lam,r.lamBind⟩)]++r.reverseRoute).getLast?=some (g.wire r.funEnd) := by
    simp only [List.getLast?_append,r.reverse_finish,Option.some_or]
  exact one.splice last (.single _) rfl (by simpa only [Pairing.involutive] using ExpandedDirection.funToArg (g:=g) r)
end
end Lamping.AG

