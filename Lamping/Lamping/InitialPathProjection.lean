import Lamping.Lamping.InitialFlow
namespace Lamping.AG
open Graph
section
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)

/-- A genuine turn between the two plug components can only be the newly
glued frontier vertex, with the same context on both sides. -/
theorem LabelledTurn.plug_cross {x : Endpoint c} {y : Endpoint r} {a b : Context}
    (h : LabelledTurn (plug c r) (AG.plugLeft c r x) (AG.plugRight c r y) a b) :
    ∃ z : F, x=.inr (.inl (.inr z)) ∧ y=.inr (.inl z) ∧ a=b := by
  rcases x with ⟨k,p⟩ | ((b | f) | ⟨w,d⟩)
  all_goals rcases y with ⟨n,q⟩ | (z | ⟨v,e⟩)
  all_goals cases h
  exact ⟨f,rfl,rfl,rfl⟩

theorem LabelledTurn.plugLeft_reflect {x y : Endpoint c} {a b : Context}
    (h : LabelledTurn (plug c r) (AG.plugLeft c r x) (AG.plugLeft c r y) a b) :
    LabelledTurn c x y a b := by
  rcases x with ⟨k,p⟩ | ((b | f) | ⟨w,d⟩)
  all_goals rcases y with ⟨n,q⟩ | ((z | f') | ⟨v,e⟩)
  all_goals cases h
  · exact .node _ _ _ ‹Traversal _ _ _ _ _ _›
  · exact .transparent _ _ _

theorem LabelledTurn.plugRight_reflect {x y : Endpoint r} {a b : Context}
    (h : LabelledTurn (plug c r) (AG.plugRight c r x) (AG.plugRight c r y) a b) :
    LabelledTurn r x y a b := by
  rcases x with ⟨k,p⟩ | (f | ⟨w,d⟩)
  all_goals rcases y with ⟨n,q⟩ | (z | ⟨v,e⟩)
  all_goals cases h
  · exact .node _ _ _ ‹Traversal _ _ _ _ _ _›
  · exact .transparent _ _ _

theorem Labelling.plugLeft_reflect {es : List (Endpoint c)} {a b : Context}
    (h : Labelling (plug c r) (es.map (AG.plugLeft c r)) a b) : Labelling c es a b := by
  induction es generalizing a b with
  | nil => cases h
  | cons x es ih =>
    cases es with
    | nil => cases h; exact .single _ _
    | cons y es =>
      cases h with
      | cons turn tail =>
        rw [plugLeft_wire] at turn
        exact .cons (turn.plugLeft_reflect c r) (ih tail)

/-- A finite actual plug path starting in the left component either stays
there, or has a first genuine frontier crossing. Its entire preceding piece
is reflected back into the source component with its original contexts. -/
theorem Labelling.plugLeft_first {x : Endpoint c} {es : List (Endpoint (plug c r))}
    {a b : Context} (h : Labelling (plug c r) (AG.plugLeft c r x::es) a b) :
    (∃ xs : List (Endpoint c), es=xs.map (AG.plugLeft c r) ∧ Labelling c (x::xs) a b) ∨
    ∃ (xs : List (Endpoint c)) (z : F) (tail : List (Endpoint (plug c r))) (mid : Context),
      es=xs.map (AG.plugLeft c r) ++ AG.plugRight c r (.inr (.inl z))::tail ∧
      Labelling c (x::xs) a mid ∧
      (x::xs).getLast?=some (c.wire (.inr (.inl (.inr z)))) ∧
      Labelling (plug c r) (AG.plugRight c r (.inr (.inl z))::tail) mid b := by
  induction es generalizing x a b with
  | nil => cases h; exact Or.inl ⟨[],rfl,.single _ _⟩
  | cons f es ih =>
    have split := (plugEnd c.label r.label).right_inv f
    generalize (plugEnd c.label r.label).invFun f = origin at split
    cases origin with
    | inl y =>
      have eq : f=AG.plugLeft c r y := split.symm
      subst f
      cases h with
      | cons turn rest =>
        rw [plugLeft_wire] at turn
        have localTurn := turn.plugLeft_reflect c r
        rcases ih rest with ⟨xs,eq,labels⟩ | ⟨xs,z,tail,mid,eq,labels,finish,last⟩
        · exact Or.inl ⟨y::xs,congrArg (AG.plugLeft c r y::·) eq,.cons localTurn labels⟩
        · refine Or.inr ⟨y::xs,z,tail,mid,congrArg (AG.plugLeft c r y::·) eq,.cons localTurn labels,?_,last⟩
          simpa using finish
    | inr y =>
      have eq : f=AG.plugRight c r y := split.symm
      subst f
      cases h with
      | cons turn rest =>
        rw [plugLeft_wire] at turn
        obtain ⟨z,hx,hy,contexts⟩ := turn.plug_cross c r
        subst y
        subst_vars
        refine Or.inr ⟨[],z,es,_,rfl,.single _ _,?_,rest⟩
        simp only [List.getLast?_cons,List.getLast?_nil,Option.some.injEq]
        have hh := congrArg c.wire.mate hx
        simpa only [Pairing.involutive] using hh

theorem LabelledTurn.plug_cross_right {x : Endpoint r} {y : Endpoint c} {a b : Context}
    (h : LabelledTurn (plug c r) (AG.plugRight c r x) (AG.plugLeft c r y) a b) :
    ∃ z : F, x=.inr (.inl z) ∧ y=.inr (.inl (.inr z)) ∧ a=b := by
  obtain ⟨z,hy,hx,contexts⟩ := h.reverse.plug_cross c r
  exact ⟨z,hx,hy,contexts.symm⟩

theorem Labelling.plugRight_reflect {es : List (Endpoint r)} {a b : Context}
    (h : Labelling (plug c r) (es.map (AG.plugRight c r)) a b) : Labelling r es a b := by
  induction es generalizing a b with
  | nil => cases h
  | cons x es ih =>
    cases es with
    | nil => cases h; exact .single _ _
    | cons y es =>
      cases h with
      | cons turn tail =>
        rw [plugRight_wire] at turn
        exact .cons (turn.plugRight_reflect c r) (ih tail)

/-- The symmetric first-crossing decomposition is needed when an encoded
body path exits its subterm into the surrounding binding/control patch. -/
theorem Labelling.plugRight_first {x : Endpoint r} {es : List (Endpoint (plug c r))}
    {a b : Context} (h : Labelling (plug c r) (AG.plugRight c r x::es) a b) :
    (∃ xs : List (Endpoint r), es=xs.map (AG.plugRight c r) ∧ Labelling r (x::xs) a b) ∨
    ∃ (xs : List (Endpoint r)) (z : F) (tail : List (Endpoint (plug c r))) (mid : Context),
      es=xs.map (AG.plugRight c r) ++ AG.plugLeft c r (.inr (.inl (.inr z)))::tail ∧
      Labelling r (x::xs) a mid ∧
      (x::xs).getLast?=some (r.wire (.inr (.inl z))) ∧
      Labelling (plug c r) (AG.plugLeft c r (.inr (.inl (.inr z)))::tail) mid b := by
  induction es generalizing x a b with
  | nil => cases h; exact Or.inl ⟨[],rfl,.single _ _⟩
  | cons f es ih =>
    have split := (plugEnd c.label r.label).right_inv f
    generalize (plugEnd c.label r.label).invFun f = origin at split
    cases origin with
    | inr y =>
      have eq : f=AG.plugRight c r y := split.symm
      subst f
      cases h with
      | cons turn rest =>
        rw [plugRight_wire] at turn
        have localTurn := turn.plugRight_reflect c r
        rcases ih rest with ⟨xs,eq,labels⟩ | ⟨xs,z,tail,mid,eq,labels,finish,last⟩
        · exact Or.inl ⟨y::xs,congrArg (AG.plugRight c r y::·) eq,.cons localTurn labels⟩
        · refine Or.inr ⟨y::xs,z,tail,mid,congrArg (AG.plugRight c r y::·) eq,.cons localTurn labels,?_,last⟩
          simpa using finish
    | inl y =>
      have eq : f=AG.plugLeft c r y := split.symm
      subst f
      cases h with
      | cons turn rest =>
        rw [plugRight_wire] at turn
        obtain ⟨z,hx,hy,contexts⟩ := turn.plug_cross_right c r
        subst y
        subst_vars
        refine Or.inr ⟨[],z,es,_,rfl,.single _ _,?_,rest⟩
        simp only [List.getLast?_cons,List.getLast?_nil,Option.some.injEq]
        have hh := congrArg r.wire.mate hx
        simpa only [Pairing.involutive] using hh
end
end Lamping.AG


