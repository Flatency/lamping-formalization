import Lamping.Lamping.InitialPatchRoutes
namespace Lamping.AG
open Graph Lambda
section FiniteRoutes
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
/-- Incidence and the actual traversal relation force a two-segment patch route. -/
theorem Labelling.one_turn_boundary {es : List (Endpoint g)} {e : Endpoint g} {a b : Context}
    (h : Labelling g es a b) (start : es.head?=some e)
    (v : N) (p q : Port (g.label v).sort)
    (arrival : g.wire e=.inl ⟨v,p⟩)
    (only : ∀ q' c d, Traversal (g.label v).index (g.label v).sort p q' c d → q'=q)
    (y z : B) (exit : g.wire (.inl ⟨v,q⟩)=.inr (.inl y))
    (finish : es.getLast?=some (g.wire (.inr (.inl z)))) :
    es=[e,.inl ⟨v,q⟩] ∧ y=z := by
  cases h with
  | single x c =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst x
    simp only [List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.some.injEq] at finish
    have eq := congrArg g.wire.mate finish
    rw [Pairing.involutive,arrival] at eq
    cases eq
  | @cons e' f tail A C D turn labels =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e'
    obtain ⟨q',eq,rule⟩ := turn.from_node v p arrival
    have same := only q' _ _ rule; subst q'; subst f
    obtain ⟨last,_⟩ := labels.boundary_terminal rfl y exit
    refine ⟨by rw [last],?_⟩
    rw [last] at finish
    simp only [List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.getD_some,Option.some.injEq] at finish
    have eq := congrArg g.wire.mate finish
    rw [Pairing.involutive,exit] at eq
    exact Sum.inl.inj (Sum.inr.inj eq)
end FiniteRoutes
/-- A function-side free variable crosses exactly its shared Fan, if present;
otherwise the patch directly wires it to its external free variable. -/
theorem appPatch_function_FV_shape (n : Nat) (f arg : Term) (x : FV f)
    (y : FV (.app f arg)) {a b : Context}
    (p : LocalPath (appPatch n f arg) (.inr (.inl (.inr x))) (.inl (.inr y)) a b) :
    y.val=x.val ∧
    (if shared : free arg x.val then
      p.edges=[.inr (.inl (.inr (.inl (.inr x)))),.inl ⟨.inr (.inr ⟨⟨x.val,shared⟩,x.property⟩),.inl ()⟩]
    else p.edges=[.inr (.inl (.inr (.inl (.inr x))))]) := by
  by_cases shared : free arg x.val
  · rw [dif_pos shared]
    have arrival : (appPatch n f arg).wire (.inr (.inl (.inr (.inl (.inr x)))))=
        .inl ⟨.inr (.inr ⟨⟨x.val,shared⟩,x.property⟩),.inr false⟩ := by simp [appPatch,appMate,shared]
    obtain ⟨eq,same⟩ := p.labeling.one_turn_boundary p.start
      (.inr (.inr ⟨⟨x.val,shared⟩,x.property⟩)) (.inr false) (.inl ()) arrival
      (fun _ _ _ rule => rule.control_aux) (.inl (.inr ⟨x.val,Or.inl x.property⟩)) (.inl (.inr y)) rfl p.finish
    exact ⟨(congrArg (fun z : Boundary (.app f arg) ⊕ (Boundary f ⊕ Boundary arg) =>
      match z with | .inl (.inr v) => v.val | _ => 0) same).symm,eq⟩
  · rw [dif_neg shared]
    obtain ⟨eq,_⟩ := p.labeling.boundary_terminal p.start (.inl (.inr ⟨x.val,Or.inl x.property⟩))
      (by simp [appPatch,appMate,shared])
    have finish := p.finish
    rw [eq] at finish
    have mate := congrArg (appPatch n f arg).wire.mate (Option.some.inj finish)
    rw [Pairing.involutive] at mate
    have boundaryEq : (.inl (.inr ⟨x.val,Or.inl x.property⟩) : Boundary (.app f arg) ⊕ (Boundary f ⊕ Boundary arg))=.inl (.inr y) := by
      simpa [appPatch,appMate,shared] using mate
    exact ⟨(congrArg (fun z : Boundary (.app f arg) ⊕ (Boundary f ⊕ Boundary arg) =>
      match z with | .inl (.inr v) => v.val | _ => 0) boundaryEq).symm,eq⟩
end Lamping.AG
namespace Lamping.AG
open Graph Lambda
/-- An argument-side FV crosses its actual Bra and then its shared Fan, if any. -/
theorem appPatch_argument_FV_shape (n : Nat) (f arg : Term) (x : FV arg)
    (y : FV (.app f arg)) {a b : Context}
    (p : LocalPath (appPatch n f arg) (.inr (.inr (.inr x))) (.inl (.inr y)) a b) :
    y.val=x.val ∧
    (if shared : free f x.val then
      p.edges=[.inr (.inl (.inr (.inr (.inr x)))),.inl ⟨.inr (.inl x),.inl ()⟩,
        .inl ⟨.inr (.inr ⟨x,shared⟩),.inl ()⟩]
    else p.edges=[.inr (.inl (.inr (.inr (.inr x)))),.inl ⟨.inr (.inl x),.inl ()⟩]) := by
  by_cases shared : free f x.val
  · rw [dif_pos shared]
    have labels := p.labeling
    have start := p.start
    have finish := p.finish
    generalize eq : p.edges=es at labels start finish ⊢
    cases labels with
    | single e c =>
      simp only [List.head?_cons,Option.some.injEq] at start; subst e
      have last : (.inr (.inl (.inr (.inr (.inr x)))) : Endpoint (appPatch n f arg))=
          (appPatch n f arg).wire (.inr (.inl (.inl (.inr y)))) := by simpa using finish
      have mate := congrArg (appPatch n f arg).wire.mate last
      rw [Pairing.involutive] at mate
      cases mate
    | @cons e e' tail A C D turn rest =>
      simp only [List.head?_cons,Option.some.injEq] at start; subst e
      obtain ⟨q,atQ,rule⟩ := turn.from_node (.inr (.inl x)) (.inr ()) rfl
      have same : q=.inl () := rule.control_aux
      subst q; subst e'
      have arrival : (appPatch n f arg).wire (.inl ⟨.inr (.inl x),.inl ()⟩)=
          .inl ⟨.inr (.inr ⟨x,shared⟩),.inr true⟩ := by simp [appPatch,appMate,shared]
      obtain ⟨last,lastBoundary⟩ := rest.one_turn_boundary rfl
        (.inr (.inr ⟨x,shared⟩)) (.inr true) (.inl ()) arrival
        (fun _ _ _ rule => rule.control_aux) (.inl (.inr ⟨x.val,Or.inr x.property⟩)) (.inl (.inr y)) rfl finish
      exact ⟨(congrArg (fun z : Boundary (.app f arg) ⊕ (Boundary f ⊕ Boundary arg) =>
        match z with | .inl (.inr v) => v.val | _ => 0) lastBoundary).symm,by rw [last]⟩
  · rw [dif_neg shared]
    obtain ⟨eq,same⟩ := p.labeling.one_turn_boundary p.start
      (.inr (.inl x)) (.inr ()) (.inl ()) rfl
      (fun _ _ _ rule => rule.control_aux) (.inl (.inr ⟨x.val,Or.inr x.property⟩)) (.inl (.inr y))
      (by simp [appPatch,appMate,shared]) p.finish
    exact ⟨(congrArg (fun z : Boundary (.app f arg) ⊕ (Boundary f ⊕ Boundary arg) =>
      match z with | .inl (.inr v) => v.val | _ => 0) same).symm,eq⟩
end Lamping.AG
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem Labelling.boundary_segment {es : List (Endpoint g)} {e : Endpoint g} {a b : Context}
    (h : Labelling g es a b) (start : es.head?=some e) (y z : B)
    (exit : g.wire e=.inr (.inl y))
    (finish : es.getLast?=some (g.wire (.inr (.inl z)))) :
    es=[e] ∧ y=z ∧ a=b := by
  obtain ⟨eq,contexts⟩ := h.boundary_terminal start y exit
  rw [eq] at finish
  have last : e=g.wire (.inr (.inl z)) := by simpa using finish
  have mate := congrArg g.wire.mate last
  rw [Pairing.involutive,exit] at mate
  exact ⟨eq,Sum.inl.inj (Sum.inr.inj mate),contexts⟩
end
/-- Every patch root-to-child path selects exactly fn-root or arg-root and
contains precisely the corresponding App turn. -/
theorem appPatch_root_to_child (n : Nat) (f arg : Term)
    (z : Boundary f ⊕ Boundary arg) {a b : Context}
    (p : LocalPath (appPatch n f arg) (.inl (.inl ())) (.inr z) a b) :
    (z=.inl (.inl ()) ∧ p.edges=[.inr (.inl (.inl (.inl ()))),.inl ⟨.inl (),.inl ()⟩] ∧ a=b) ∨
    (z=.inr (.inl ()) ∧ p.edges=[.inr (.inl (.inl (.inl ()))),.inl ⟨.inl (),appArg⟩] ∧ a=b) := by
  have labels := p.labeling
  have start := p.start
  have finish := p.finish
  generalize eq : p.edges=es at labels start finish ⊢
  cases labels with
  | single e c =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e
    have last : (.inr (.inl (.inl (.inl ()))) : Endpoint (appPatch n f arg))=
        (appPatch n f arg).wire (.inr (.inl (.inr z))) := by simpa using finish
    have mate := congrArg (appPatch n f arg).wire.mate last
    rw [Pairing.involutive] at mate
    cases mate
  | @cons e e' tail A C D turn rest =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e
    obtain ⟨q,atQ,rule⟩ := turn.from_node (.inl ()) appCtx rfl
    have contexts : a=C := rule.proper_context
    cases q with
    | inl u =>
      cases u; subst e'
      obtain ⟨last,same,lastContexts⟩ := rest.boundary_segment rfl (.inr (.inl (.inl ()))) (.inr z) rfl finish
      exact Or.inl ⟨(Sum.inr.inj same).symm,by rw [last],contexts.trans lastContexts⟩
    | inr q =>
      cases q with
      | false => exact False.elim (rule.distinct rfl)
      | true =>
        subst e'
        obtain ⟨last,same,lastContexts⟩ := rest.boundary_segment rfl (.inr (.inr (.inl ()))) (.inr z) rfl finish
        exact Or.inr ⟨(Sum.inr.inj same).symm,by rw [last]; rfl,contexts.trans lastContexts⟩
end Lamping.AG
namespace Lamping.AG
open Graph Lambda
/-- A used-lambda patch forwards only successor FVs to its external interface. -/
theorem lambdaUsed_FV_external_shape (n : Nat) (body : Term) (used : free body 0)
    (x : FV body) (y : FV (.lam body)) {a b : Context}
    (p : LocalPath (lambdaUsed n body used) (.inr (.inr x)) (.inl (.inr y)) a b) :
    x.val=y.val+1 ∧ p.edges=[.inr (.inl (.inr (.inr x)))] ∧ a=b := by
  obtain ⟨k,hk⟩ := x
  cases k with
  | zero =>
    obtain ⟨eq,_⟩ := p.labeling.binding_terminal p.start () rfl lamBind (HEq.rfl) rfl
    have finish := p.finish
    rw [eq] at finish
    cases finish
  | succ k =>
    obtain ⟨eq,same,contexts⟩ := p.labeling.boundary_segment p.start
      (.inl (.inr ⟨k,hk⟩)) (.inl (.inr y)) rfl p.finish
    have values : k=y.val := congrArg (fun z : Boundary (.lam body) ⊕ Boundary body =>
      match z with | .inl (.inr v) => v.val | _ => 0) same
    exact ⟨congrArg (·+1) values,eq,contexts⟩
/-- An unused-lambda patch has exactly the same successor-FV forwarding. -/
theorem lambdaUnused_FV_external_shape (n : Nat) (body : Term) (unused : ¬free body 0)
    (x : FV body) (y : FV (.lam body)) {a b : Context}
    (p : LocalPath (lambdaUnused n body unused) (.inr (.inr x)) (.inl (.inr y)) a b) :
    x.val=y.val+1 ∧ p.edges=[.inr (.inl (.inr (.inr x)))] ∧ a=b := by
  obtain ⟨k,hk⟩ := x
  cases k with
  | zero => exact False.elim (unused hk)
  | succ k =>
    obtain ⟨eq,same,contexts⟩ := p.labeling.boundary_segment p.start
      (.inl (.inr ⟨k,hk⟩)) (.inl (.inr y)) rfl p.finish
    have values : k=y.val := congrArg (fun z : Boundary (.lam body) ⊕ Boundary body =>
      match z with | .inl (.inr v) => v.val | _ => 0) same
    exact ⟨congrArg (·+1) values,eq,contexts⟩
end Lamping.AG
