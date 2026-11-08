import Lamping.Lamping.InitialBoundaryProjection
namespace Lamping.AG.InitialOffsets
open Graph Lambda
section UnionBoundary
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
private theorem map_last_reflect {S T : Type} (f : S → T) (injective : Function.Injective f)
    (xs : List S) (y : S) (eq : (xs.map f).getLast?=some (f y)) : xs.getLast?=some y := by
  rw [List.getLast?_map] at eq
  cases last : xs.getLast? with
  | none => simp [last] at eq
  | some v =>
    simp only [last,Option.map_some,Option.some.injEq] at eq
    rw [injective eq]
theorem union_sides_distinct (x : Endpoint g) (y : Endpoint h) : unionL g h x≠unionR g h y := by
  rcases x with ⟨n,p⟩ | (b | ⟨w,d⟩)
  all_goals rcases y with ⟨n',p'⟩ | (c | ⟨v,d⟩)
  all_goals intro eq; cases eq

theorem LocalPath.unionL_source (x : B) (y : B⊕C) {a b : Context}
    (p : LocalPath (unionNet g h) (.inl x) y a b) :
    ∃ z : B, y=.inl z ∧ ∃ q : LocalPath g x z a b, p.edges=q.edges.map (unionL g h) := by
  rcases p with ⟨es,start,finish,labels⟩
  cases es with
  | nil => simp at start
  | cons e tail =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e
    change Labelling (unionNet g h) (unionL g h (.inr (.inl x))::tail) a b at labels
    obtain ⟨xs,eq,localLabels⟩ := labels_unionL_stay g h labels
    rw [eq] at finish
    change ((.inr (.inl x)::xs).map (unionL g h)).getLast?=some ((unionNet g h).wire (.inr (.inl y))) at finish
    cases y with
    | inl z =>
      change ((.inr (.inl x)::xs).map (unionL g h)).getLast?=some ((unionNet g h).wire (unionL g h (.inr (.inl z)))) at finish
      rw [show (unionNet g h).wire (unionL g h (.inr (.inl z)))=unionL g h (g.wire (.inr (.inl z))) from union_left g h _] at finish
      have localFinish := map_last_reflect (unionL g h) (unionL_injective g h) _ _ finish
      exact ⟨z,rfl,⟨_,rfl,localFinish,localLabels⟩,by change (unionL g h (.inr (.inl x))::tail)=_; rw [eq]; rfl⟩
    | inr z =>
      change ((.inr (.inl x)::xs).map (unionL g h)).getLast?=some ((unionNet g h).wire (unionR g h (.inr (.inl z)))) at finish
      rw [show (unionNet g h).wire (unionR g h (.inr (.inl z)))=unionR g h (h.wire (.inr (.inl z))) from union_right g h _,List.getLast?_map] at finish
      cases last : (.inr (.inl x)::xs).getLast? with
      | none => simp [last] at finish
      | some v =>
        simp only [last,Option.map_some,Option.some.injEq] at finish
        exact False.elim (union_sides_distinct g h v _ finish)

theorem LocalPath.unionR_source (x : C) (y : B⊕C) {a b : Context}
    (p : LocalPath (unionNet g h) (.inr x) y a b) :
    ∃ z : C, y=.inr z ∧ ∃ q : LocalPath h x z a b, p.edges=q.edges.map (unionR g h) := by
  rcases p with ⟨es,start,finish,labels⟩
  cases es with
  | nil => simp at start
  | cons e tail =>
    simp only [List.head?_cons,Option.some.injEq] at start; subst e
    change Labelling (unionNet g h) (unionR g h (.inr (.inl x))::tail) a b at labels
    obtain ⟨xs,eq,localLabels⟩ := labels_unionR_stay g h labels
    rw [eq] at finish
    change ((.inr (.inl x)::xs).map (unionR g h)).getLast?=some ((unionNet g h).wire (.inr (.inl y))) at finish
    cases y with
    | inr z =>
      change ((.inr (.inl x)::xs).map (unionR g h)).getLast?=some ((unionNet g h).wire (unionR g h (.inr (.inl z)))) at finish
      rw [show (unionNet g h).wire (unionR g h (.inr (.inl z)))=unionR g h (h.wire (.inr (.inl z))) from union_right g h _] at finish
      have localFinish := map_last_reflect (unionR g h) (unionR_injective g h) _ _ finish
      exact ⟨z,rfl,⟨_,rfl,localFinish,localLabels⟩,by change (unionR g h (.inr (.inl x))::tail)=_; rw [eq]; rfl⟩
    | inl z =>
      change ((.inr (.inl x)::xs).map (unionR g h)).getLast?=some ((unionNet g h).wire (unionL g h (.inr (.inl z)))) at finish
      rw [show (unionNet g h).wire (unionL g h (.inr (.inl z)))=unionL g h (g.wire (.inr (.inl z))) from union_left g h _,List.getLast?_map] at finish
      cases last : (.inr (.inl x)::xs).getLast? with
      | none => simp [last] at finish
      | some v =>
        simp only [last,Option.map_some,Option.some.injEq] at finish
        exact False.elim (union_sides_distinct g h _ v finish.symm)
end UnionBoundary
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
section WordMaps
variable {K R B F W V : Type} [FiniteNames K] [FiniteNames R] [FiniteNames B]
  [FiniteNames F] [FiniteNames W] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature R F V)
theorem allEvents_plugLeft (es : List (Endpoint c)) :
    allEvents (plug c r) (es.map (plugLeft c r))=allEvents c es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change arrivalEvents (plug c r) (plugLeft c r e) ++ allEvents (plug c r) (es.map (plugLeft c r))=
      arrivalEvents c e ++ allEvents c es
    rw [arrivalEvents_plugLeft,ih]
theorem allEvents_three_pieces (xs : List (Endpoint c)) (zs : List (Endpoint r))
    (ys : List (Endpoint c)) :
    allEvents (plug c r) (xs.map (plugLeft c r) ++ zs.map (plugRight c r) ++ ys.map (plugLeft c r))=
    allEvents c xs ++ allEvents r zs ++ allEvents c ys := by
  change _=allEvents c xs ++ allEvents r zs ++ allEvents c ys
  simp only [allEvents,List.flatMap_append]
  rw [←allEvents,←allEvents,←allEvents,allEvents_plugLeft,allEvents_plugRight,allEvents_plugLeft]
  rfl
end WordMaps
section UnionWords
variable {N M B C W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
  [FiniteNames C] [FiniteNames W] [FiniteNames V]
variable (g : Net signature N B W) (h : Net signature M C V)
theorem arrivalEvents_unionL (e : Endpoint g) :
    arrivalEvents (unionNet g h) (unionL g h e)=arrivalEvents g e := by
  unfold arrivalEvents
  rw [show (unionNet g h).wire (unionL g h e)=unionL g h (g.wire e) from union_left g h e]
  rcases g.wire e with ⟨n,p⟩ | (b | ⟨w,d⟩) <;> rfl
theorem arrivalEvents_unionR (e : Endpoint h) :
    arrivalEvents (unionNet g h) (unionR g h e)=arrivalEvents h e := by
  unfold arrivalEvents
  rw [show (unionNet g h).wire (unionR g h e)=unionR g h (h.wire e) from union_right g h e]
  rcases h.wire e with ⟨n,p⟩ | (c | ⟨w,d⟩) <;> rfl
theorem allEvents_unionL (es : List (Endpoint g)) :
    allEvents (unionNet g h) (es.map (unionL g h))=allEvents g es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change arrivalEvents (unionNet g h) (unionL g h e) ++ allEvents (unionNet g h) (es.map (unionL g h))=
      arrivalEvents g e ++ allEvents g es
    rw [arrivalEvents_unionL,ih]
theorem allEvents_unionR (es : List (Endpoint h)) :
    allEvents (unionNet g h) (es.map (unionR g h))=allEvents h es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change arrivalEvents (unionNet g h) (unionR g h e) ++ allEvents (unionNet g h) (es.map (unionR g h))=
      arrivalEvents h e ++ allEvents h es
    rw [arrivalEvents_unionR,ih]
end UnionWords
section Separation
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {bp : B → Bool} {wp : W → Bool}
theorem LocalPath.no_proper_to_variable {x y : B} {a b : Context}
    (p : LocalPath g x y a b) (separated : VariableSeparated g bp wp)
    (hx : bp x=false) (hy : bp y=true) : False :=
  p.reverse.labeling.no_variable_exit separated p.reverse.start hy p.reverse.finish hx
end Separation
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
theorem FreeOccurrence.shape_cast {t : Term} {i j : Nat} (h : i=j) (p : FreeOccurrence t i) :
    (h ▸ p).shape=p.shape := by cases h; rfl
/-- Every actual initial root-to-free-variable path has the independently defined
syntax occurrence control shape. There is no shape/length/one-Cro input. -/
theorem encode_FV_shape (t : Term) (n : Nat) (x : FV t) {a b : Context}
    (p : LocalPath (encode n t).net (.inl ()) (.inr x) a b) :
    ∃ occurrence : FreeOccurrence t x.val,
      allEvents (encode n t).net p.edges=occurrence.shape.events n := by
  induction t generalizing n a b with
  | var k =>
    obtain ⟨value,freeValue⟩ := x
    change value=k at freeValue
    subst value
    obtain ⟨eq,_⟩ := p.labeling.one_turn_boundary p.start () (.inr ()) (.inl ()) rfl
      (fun _ _ _ rule => rule.control_aux) (.inr ⟨k,rfl⟩) (.inr ⟨k,rfl⟩) rfl p.finish
    exact ⟨.leaf k,by rw [eq]; rfl⟩
  | lam body ih =>
    revert p
    dsimp only [encode]
    obtain ⟨vp,rflow⟩ := encode_flow body n
    by_cases used : free body 0
    · rw [dif_pos used]
      intro p
      obtain ⟨z,z',mid,last,first,middle,suffix,entry,exit,eq⟩ := LocalPath.outer_child
        (lambdaUsed n body used) (encode n body).net (lambdaUsed_flow n body used) rflow
        (lambdaUsed_noReturn n body used) (.inl ()) (.inr x) rfl
        (fun _ _ path => LocalPath.no_proper_to_variable path (lambdaUsed_variableSeparated n body used) rfl rfl) p
      obtain ⟨firstEq,rfl,_⟩ := lambdaUsed_root_to_child n body used z first
      cases z' with
      | inl u => cases exit
      | inr fv =>
        obtain ⟨value,suffixEq,_⟩ := lambdaUsed_FV_external_shape n body used fv x suffix
        rcases fv with ⟨k,hk⟩
        dsimp at value; subst k
        obtain ⟨occ,shape⟩ := ih n ⟨x.val+1,hk⟩ middle
        refine ⟨.lambda occ,?_⟩
        rw [eq,allEvents_three_pieces,firstEq,suffixEq]
        change [] ++ allEvents (encode n body).net middle.edges ++ []=_
        simpa only [List.nil_append,List.append_nil] using shape
    · rw [dif_neg used]
      intro p
      obtain ⟨z,z',mid,last,first,middle,suffix,entry,exit,eq⟩ := LocalPath.outer_child
        (lambdaUnused n body used) (encode n body).net (lambdaUnused_flow n body used) rflow
        (lambdaUnused_noReturn n body used) (.inl ()) (.inr x) rfl
        (fun _ _ path => LocalPath.no_proper_to_variable path (lambdaUnused_variableSeparated n body used) rfl rfl) p
      obtain ⟨firstEq,rfl,_⟩ := lambdaUnused_root_to_child n body used z first
      cases z' with
      | inl u => cases exit
      | inr fv =>
        obtain ⟨value,suffixEq,_⟩ := lambdaUnused_FV_external_shape n body used fv x suffix
        rcases fv with ⟨k,hk⟩
        dsimp at value; subst k
        obtain ⟨occ,shape⟩ := ih n ⟨x.val+1,hk⟩ middle
        refine ⟨.lambda occ,?_⟩
        rw [eq,allEvents_three_pieces,firstEq,suffixEq]
        change [] ++ allEvents (encode n body).net middle.edges ++ []=_
        simpa only [List.nil_append,List.append_nil] using shape
  | app f arg hf ha =>
    dsimp only [encode] at p ⊢
    obtain ⟨wp,fnFlow⟩ := encode_flow f n
    obtain ⟨vp,argFlow⟩ := encode_flow arg (n+1)
    have unionFlow := FlowOn.union (g:=(encode n f).net) (h:=(encode (n+1) arg).net)
      (bp:=initialBoundaryPolarity) (cp:=initialBoundaryPolarity) (wp:=wp) (vp:=vp) fnFlow argFlow
    obtain ⟨z,z',mid,last,first,middle,suffix,entry,exit,eq⟩ := LocalPath.outer_child
      (appPatch n f arg) (unionNet (encode n f).net (encode (n+1) arg).net)
      (appPatch_flow n f arg) unionFlow (appPatch_noReturn n f arg) (.inl ()) (.inr x) rfl
      (fun _ _ path => LocalPath.no_proper_to_variable path (appPatch_variableSeparated n f arg) rfl rfl) p
    rcases appPatch_root_to_child n f arg z first with ⟨rfl,firstEq,_⟩ | ⟨rfl,firstEq,_⟩
    · obtain ⟨v,rfl,child,childEq⟩ := LocalPath.unionL_source (encode n f).net (encode (n+1) arg).net (.inl ()) z' middle
      cases v with
      | inl u => cases exit
      | inr fv =>
        obtain ⟨value,suffixEq⟩ := appPatch_function_FV_shape n f arg fv x suffix
        obtain ⟨occ,shape⟩ := hf n fv child
        let occurrence : FreeOccurrence (.app f arg) x.val := value.symm ▸ FreeOccurrence.function arg occ
        refine ⟨occurrence,?_⟩
        rw [eq,allEvents_three_pieces,firstEq,childEq,allEvents_unionL]
        by_cases shared : free arg fv.val
        · rw [dif_pos shared] at suffixEq
          rw [suffixEq]
          simp only [allEvents,List.flatMap_cons,List.flatMap_nil,arrivalEvents,appPatch,appMate,shared,dif_pos,appLabels,label,eventOfPort,Option.toList,List.append_nil]
          change [] ++ allEvents (encode n f).net child.edges ++ [.fan n false]=_
          rw [List.nil_append,shape]
          rw [show occurrence.shape=(FreeOccurrence.function arg occ).shape from FreeOccurrence.shape_cast value.symm _]
          simp [FreeOccurrence.shape,shared,Shape.addFan_events]
        · rw [dif_neg shared] at suffixEq
          rw [suffixEq]
          simp only [allEvents,List.flatMap_cons,List.flatMap_nil,arrivalEvents,appPatch,appMate,shared,appLabels,label,eventOfPort,Option.toList,List.append_nil]
          change [] ++ allEvents (encode n f).net child.edges ++ []=_
          rw [List.nil_append,List.append_nil,shape]
          rw [show occurrence.shape=(FreeOccurrence.function arg occ).shape from FreeOccurrence.shape_cast value.symm _]
          simp [FreeOccurrence.shape,shared]
    · obtain ⟨v,rfl,child,childEq⟩ := LocalPath.unionR_source (encode n f).net (encode (n+1) arg).net (.inl ()) z' middle
      cases v with
      | inl u => cases exit
      | inr fv =>
        obtain ⟨value,suffixEq⟩ := appPatch_argument_FV_shape n f arg fv x suffix
        obtain ⟨occ,shape⟩ := ha (n+1) fv child
        let occurrence : FreeOccurrence (.app f arg) x.val := value.symm ▸ FreeOccurrence.argument f occ
        refine ⟨occurrence,?_⟩
        rw [eq,allEvents_three_pieces,firstEq,childEq,allEvents_unionR]
        by_cases shared : free f fv.val
        · rw [dif_pos shared] at suffixEq
          rw [suffixEq]
          simp only [allEvents,List.flatMap_cons,List.flatMap_nil,arrivalEvents,appPatch,appMate,shared,dif_pos,appLabels,label,eventOfPort,Option.toList,List.append_nil]
          change [] ++ allEvents (encode (n+1) arg).net child.edges ++ [.bra n,.fan n true]=_
          rw [List.nil_append,shape]
          rw [show occurrence.shape=(FreeOccurrence.argument f occ).shape from FreeOccurrence.shape_cast value.symm _]
          simp [FreeOccurrence.shape,shared,Shape.events,List.append_assoc]
        · rw [dif_neg shared] at suffixEq
          rw [suffixEq]
          simp only [allEvents,List.flatMap_cons,List.flatMap_nil,arrivalEvents,appPatch,appMate,shared,appLabels,label,eventOfPort,Option.toList,List.append_nil]
          change [] ++ allEvents (encode (n+1) arg).net child.edges ++ [.bra n]=_
          rw [List.nil_append,shape]
          rw [show occurrence.shape=(FreeOccurrence.argument f occ).shape from FreeOccurrence.shape_cast value.symm _]
          simp [FreeOccurrence.shape,shared,Shape.events]
end Lamping.AG.InitialOffsets
namespace Lamping.AG.InitialOffsets
open Graph Lambda
section RawWord
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
theorem RawLoop.events_all {es : List (Endpoint g)} {a b : Context}
    (loop : RawLoop g es a b) : eventsOfEdges g es=allEvents g es := by
  apply events_eq_allEvents
  intro e he
  have same : e=g.wire (.inl ⟨loop.binder,loop.bind⟩) := Option.some.inj (he.symm.trans loop.finish)
  unfold arrivalEvents
  rw [same,Pairing.involutive]
  change (eventOfPort (g.label loop.binder).index (g.label loop.binder).sort loop.bind).toList=[]
  have noEvent (i : Nat) {k : Kind} (h : k=.op .lam) (p : Port k) : eventOfPort i k p=none := by subst k; rfl
  rw [noEvent _ loop.isLam loop.bind]
  rfl
end RawWord
end Lamping.AG.InitialOffsets

namespace Lamping.AG.InitialOffsets
open Graph Lambda
/-- Every actual initial raw loop has one Cro and the exact descending-level
Bra/Fan shape, at its own binder's index. This extracts the shape from the graph. -/
theorem encode_rawLoop_shape (t : Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) (a b : Context)
    (loop : RawLoop (encode n t).net es a b) :
    ∃ shape : Shape, allEvents (encode n t).net es=shape.events ((encode n t).net.label loop.binder).index := by
  induction t generalizing n a b with
  | var k => have impossible:=loop.isLam; change Kind.op .cro=Kind.op .lam at impossible; cases impossible
  | lam body ih =>
    revert es
    dsimp only [encode]
    obtain ⟨vp,rflow⟩ := encode_flow body n
    by_cases used : free body 0
    · rw [dif_pos used]
      intro es loop
      cases binder : loop.binder with
      | inl u =>
        cases u
        obtain ⟨p,word⟩ := lambdaUsed_rawLoop_events n body used (encode n body).net vp rflow loop binder
        obtain ⟨occ,shape⟩ := encode_FV_shape body n ⟨0,used⟩ p
        refine ⟨occ.shape,?_⟩
        change allEvents (plug (lambdaUsed n body used) (encode n body).net) es=occ.shape.events n
        rw [←loop.events_all,word,LocalPath.events_all,shape]
      | inr v =>
        obtain ⟨rs,child,childBinder,eq⟩ := rawLoop_plugRight (lambdaUsed n body used) (encode n body).net
          (lambdaUsed_flow n body used) rflow (lambdaUsed_noReturn n body used) loop v binder
        obtain ⟨shape,word⟩ := ih n rs a b child
        rw [childBinder] at word
        refine ⟨shape,?_⟩
        rw [eq,allEvents_plugRight]
        exact word
    · rw [dif_neg used]
      intro es loop
      cases binder : loop.binder with
      | inl patch =>
        cases patch with
        | inl u =>
          cases u
          exact False.elim (lambdaUnused_no_rawLoop n body used (encode n body).net vp rflow loop binder)
        | inr u => have impossible:=loop.isLam; rw [binder] at impossible; cases impossible
      | inr v =>
        obtain ⟨rs,child,childBinder,eq⟩ := rawLoop_plugRight (lambdaUnused n body used) (encode n body).net
          (lambdaUnused_flow n body used) rflow (lambdaUnused_noReturn n body used) loop v binder
        obtain ⟨shape,word⟩ := ih n rs a b child
        rw [childBinder] at word
        refine ⟨shape,?_⟩
        rw [eq,allEvents_plugRight]
        exact word
  | app f arg hf ha =>
    dsimp only [encode] at loop ⊢
    cases binder : loop.binder with
    | inl patch =>
      rcases patch with u | (x | x)
      all_goals have impossible:=loop.isLam; rw [binder] at impossible; cases impossible
    | inr v =>
      obtain ⟨wp,fnFlow⟩ := encode_flow f n
      obtain ⟨vp,argFlow⟩ := encode_flow arg (n+1)
      have unionFlow := FlowOn.union (g:=(encode n f).net) (h:=(encode (n+1) arg).net)
        (bp:=initialBoundaryPolarity) (cp:=initialBoundaryPolarity) (wp:=wp) (vp:=vp) fnFlow argFlow
      obtain ⟨rs,child,childBinder,eq⟩ := rawLoop_plugRight (appPatch n f arg)
        (unionNet (encode n f).net (encode (n+1) arg).net) (appPatch_flow n f arg) unionFlow
        (appPatch_noReturn n f arg) loop v binder
      cases v with
      | inl v =>
        obtain ⟨ss,localLoop,localBinder,localEq⟩ := rawLoop_unionL (encode n f).net (encode (n+1) arg).net child v childBinder
        obtain ⟨shape,word⟩ := hf n ss a b localLoop
        rw [localBinder] at word
        refine ⟨shape,?_⟩
        rw [eq,allEvents_plugRight,localEq,allEvents_unionL]
        exact word
      | inr v =>
        obtain ⟨ss,localLoop,localBinder,localEq⟩ := rawLoop_unionR (encode n f).net (encode (n+1) arg).net child v childBinder
        obtain ⟨shape,word⟩ := ha (n+1) ss a b localLoop
        rw [localBinder] at word
        refine ⟨shape,?_⟩
        rw [eq,allEvents_plugRight,localEq,allEvents_unionR]
        exact word
end Lamping.AG.InitialOffsets

namespace Lamping.AG.InitialOffsets
open Graph Lambda
/-- The authorized corrected Exercise 3.5.25 formula for every actual initial
raw loop. Marker strings may decorate entire intermediate pairs. -/
theorem encode_rawLoop_corrected (t : Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) (a b : Context)
    (loop : RawLoop (encode n t).net es a b) :
    ∃ shape : Shape,
      eventsOfEdges (encode n t).net es=shape.events ((encode n t).net.label loop.binder).index ∧
      ((eventsOfEdges (encode n t).net es).filter Event.isCro).length=1 ∧
      ((eventsOfEdges (encode n t).net es).filter Event.isBra).length=shape.offset ∧
      b=a.replace ((encode n t).net.label loop.binder).index
        ((a.tail (((encode n t).net.label loop.binder).index+shape.offset)).cons
          (shape.level a ((encode n t).net.label loop.binder).index)) := by
  obtain ⟨shape,word⟩ := encode_rawLoop_shape t n es a b loop
  rw [←loop.events_all] at word
  have run := InitialLabelling.events_run (encode_rawLoop_initial t n es loop)
  rw [word] at run
  exact ⟨shape,word,by rw [word,Shape.croissant_count],by rw [word,Shape.bracket_count],
    corrected_program_all_runs shape _ a b run⟩
end Lamping.AG.InitialOffsets

namespace Lamping.AG.InitialOffsets
open Graph Lambda
theorem Passage.bra_event {i k p q a b} (h : Passage i k p q a b) :
    (((eventOfPort i k p).toList).filter Event.isBra).length=(if k==Kind.op .bra then 1 else 0) := by
  cases h <;> rfl
section BraCount
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
def kindIsBra (k : Kind) : Bool := k==Kind.op .bra
def arrivalBraCount (e : Endpoint g) : Nat :=
  match g.wire e with
  | .inl ⟨v,_⟩ => if kindIsBra (g.label v).sort then 1 else 0
  | _ => 0

theorem bracketOffset_cons (e f : Endpoint g) (es : List (Endpoint g)) :
    bracketOffset g (e::f::es)=arrivalBraCount g e+bracketOffset g (f::es) := by
  unfold bracketOffset crossedKinds arrivalBraCount
  rcases arrival : g.wire e with ⟨v,p⟩ | (b | ⟨w,d⟩)
  · cases kind : (g.label v).sort with
    | garbage => simp [List.dropLast,arrival,kind,kindIsBra]
    | op op => cases op <;> simp [List.dropLast,arrival,kind,kindIsBra] <;> omega
  · simp [List.dropLast,arrival]
  · simp [List.dropLast,arrival]

theorem InitialTurn.bra_count {x y : Endpoint g} {a b : Context}
    (h : AG.InitialTurn (g:=g) x y a b) (e : Endpoint g) (arrives : g.wire e=x) :
    ((arrivalEvents g e).filter Event.isBra).length=arrivalBraCount g e := by
  unfold arrivalEvents arrivalBraCount
  rw [arrives]
  cases h with
  | node v p q rule => exact Passage.bra_event rule
  | transparent => rfl

theorem InitialLabelling.bra_count {es : List (Endpoint g)} {a b : Context}
    (h : AG.InitialLabelling (g:=g) es a b) :
    ((eventsOfEdges g es).filter Event.isBra).length=bracketOffset g es := by
  induction h with
  | single => rfl
  | @cons e f es a b c turn tail ih =>
    change ((arrivalEvents g e ++ eventsOfEdges g (f::es)).filter Event.isBra).length=_
    rw [List.filter_append,List.length_append,ih,InitialTurn.bra_count g turn e rfl,bracketOffset_cons]
end BraCount
/-- The program offset is exactly the number of physically crossed Bra nodes,
with repetitions counted as in the source path definition. -/
theorem encode_rawLoop_offset (t : Term) (n : Nat)
    (es : List (Endpoint (encode n t).net)) (a b : Context)
    (loop : RawLoop (encode n t).net es a b) :
    ∃ shape : Shape, eventsOfEdges (encode n t).net es=shape.events ((encode n t).net.label loop.binder).index ∧
      shape.offset=bracketOffset (encode n t).net es ∧
      b=a.replace ((encode n t).net.label loop.binder).index
        ((a.tail (((encode n t).net.label loop.binder).index+shape.offset)).cons
          (shape.level a ((encode n t).net.label loop.binder).index)) := by
  obtain ⟨shape,word,_,count,formula⟩ := encode_rawLoop_corrected t n es a b loop
  have physical := InitialLabelling.bra_count (encode n t).net (encode_rawLoop_initial t n es loop)
  exact ⟨shape,word,count.symm.trans physical,formula⟩
end Lamping.AG.InitialOffsets
