import Lamping.Lamping.ActionCanonicalRoutes
import Lamping.Lamping.CancellationSourceContraction
import Lamping.Lamping.CancellationCanonicalPrefixes
import Lamping.Lamping.TypedWireSourceContraction
namespace Lamping.AG
open Graph
section
variable {K B F W N D V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames F]
  [FiniteNames W] [FiniteNames N] [FiniteNames D] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature Empty F Empty)
variable (g : Net signature N D V) (embed : Endpoint c → Endpoint g)
variable (fronts : F → List (Endpoint g))
/-- Unlike WireBlockResidual, a frontier has one fixed physical fronts. -/
inductive CanonicalWireResidual : List (PlugSegment c r) → List (Endpoint g) → Prop where
 | single (e : Endpoint c) : CanonicalWireResidual [.inl e] [embed e]
 | outside {e f : Endpoint c} {tail old}
     (rest : CanonicalWireResidual (.inl f::tail) old) :
     CanonicalWireResidual (.inl e::.inl f::tail) (embed e::old)
 | through {e : Endpoint c} {f : F} {tail old}
     (start : (fronts f++[embed (.inr (.inl (.inr (wireBoundaryMate r f))))]).head?=some (embed e))
     (rest : CanonicalWireResidual (.inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) old) :
     CanonicalWireResidual (.inl e::.inr (.inr (.inl f))::
       .inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) (fronts f++old)

theorem CanonicalWireResidual.erase
    (relation : CanonicalWireResidual c r g embed fronts raw old) :
    WireBlockResidual c r g embed raw old := by
  induction relation with
  | single e => exact .single e
  | outside rest ih => exact .outside ih
  | @through e f tail old start rest ih => exact .through (fronts f) start ih

theorem CanonicalWireResidual.source_unique
    (first : CanonicalWireResidual c r g embed fronts raw left)
    (second : CanonicalWireResidual c r g embed fronts raw right) : left=right := by
  induction first generalizing right with
  | single e => cases second; rfl
  | outside rest ih =>
    cases second with
    | outside other => exact congrArg (_::·) (ih other)
  | @through e f tail old start rest ih =>
    cases second with
    | through otherStart other => exact congrArg (List.append (fronts f)) (ih other)
theorem Labelling.contract_canonical_typed_wire_source
    (embedInjective : Function.Injective embed)
    (wiring : ∀ e,g.wire (embed e)=embed (c.wire e))
    (outside : ∀ {e : Endpoint c} {f : Endpoint g} {a b : Context},
      LabelledTurn g (g.wire (embed e)) f a b →
      (∃ h,f=embed h ∧LabelledTurn c (c.wire e) h a b) ∨
      ∃ frontier,c.wire e=.inr (.inl (.inr frontier)))
    (crossing : ∀ (frontier : F) {es : List (Endpoint g)} {a b : Context},
      Labelling g es a b → (∃ k,accessKind g es=some k) →
      es.head?=some (g.wire (embed (.inr (.inl (.inr frontier))))) →
      ∃ rest,es=fronts frontier++embed (.inr (.inl (.inr (wireBoundaryMate r frontier))))::rest ∧
        fronts frontier≠[] ∧Labelling g (embed (.inr (.inl (.inr (wireBoundaryMate r frontier))))::rest) a b)
    {es : List (Endpoint g)} {a b : Context} (labels : Labelling g es a b)
    (typed : ∃ k,accessKind g es=some k)
    (first last : Endpoint c) (head : es.head?=some (embed first))
    (finish : es.getLast?=some (embed last)) :
    ∃ raw,WireExcursions c r raw a b ∧CanonicalWireResidual c r g embed fronts raw es ∧
      raw.head?=some (.inl first) ∧raw.getLast?=some (.inl last) := by
  induction bound : es.length using Nat.strongRecOn generalizing es a b first last with
  | ind size ih =>
    cases labels with
    | single e a =>
      have initial := Option.some.inj head
      subst e
      have terminal := embedInjective (Option.some.inj finish)
      subst last
      exact ⟨[.inl first],.single first a,.single first,rfl,rfl⟩
    | @cons e f tail a middle b turn remaining =>
      have initial := Option.some.inj head
      subst e
      rcases outside turn with ⟨next,departure,localTurn⟩ | ⟨frontier,arrival⟩
      · subst f
        have tailTyped : ∃ k,accessKind g (embed next::tail)=some k := by
          simpa only [accessKind,List.getLast?_cons_cons] using typed
        have tailFinish : (embed next::tail).getLast?=some (embed last) := by
          simpa only [List.getLast?_cons_cons] using finish
        obtain ⟨raw,path,residual,start,endEq⟩ := ih (embed next::tail).length (by simp only [List.length_cons] at bound ⊢; omega)
          remaining tailTyped next last rfl tailFinish rfl
        obtain ⟨post,rawSplit⟩ := List.head?_eq_some_iff.mp start
        rw [rawSplit] at path residual
        refine ⟨.inl first::.inl next::post,.outside localTurn path,.outside residual,rfl,?_⟩
        simpa only [rawSplit,List.getLast?_cons_cons] using endEq
      · have enters : embed first=g.wire (embed (.inr (.inl (.inr frontier)))) := by
          have same : g.wire (embed first)=embed (.inr (.inl (.inr frontier))) := by rw [wiring,arrival]
          have inverse := congrArg g.wire.mate same
          simpa only [Pairing.involutive] using inverse
        obtain ⟨rest,split,frontNonempty,suffixLabels⟩ := crossing frontier
          (.cons turn remaining) typed (by simpa only [List.head?_cons] using congrArg some enters)
        let front := fronts frontier
        change (embed first :: f :: tail) = front ++ _ at split
        change front ≠ [] at frontNonempty
        let paired : Endpoint c := .inr (.inl (.inr (wireBoundaryMate r frontier)))
        have tailTyped : ∃ k,accessKind g (embed paired::rest)=some k := by
          simpa only [split,accessKind,List.getLast?_append,List.getLast?_cons,Option.some_or] using typed
        have tailFinish : (embed paired::rest).getLast?=some (embed last) := by
          simpa only [split,List.getLast?_append,List.getLast?_cons,Option.some_or] using finish
        have smaller : (embed paired::rest).length<size := by
          have lengths := congrArg List.length split
          have positive := List.length_pos_iff.mpr frontNonempty
          simp only [List.length_cons,List.length_append] at lengths bound ⊢
          omega
        obtain ⟨raw,path,residual,start,endEq⟩ := ih (embed paired::rest).length smaller
          suffixLabels tailTyped paired last rfl tailFinish rfl
        obtain ⟨post,rawSplit⟩ := List.head?_eq_some_iff.mp start
        rw [rawSplit] at path residual
        have blockHead : (front++[embed paired]).head?=some (embed first) := by
          cases frontEq : front with
          | nil => exact False.elim (frontNonempty frontEq)
          | cons x front => simpa only [split,frontEq,List.cons_append,List.head?_cons] using head
        refine ⟨.inl first::.inr (.inr (.inl frontier))::.inl paired::post,.through arrival path,?_,rfl,?_⟩
        · rw [split]
          exact .through blockHead residual
        · simpa only [rawSplit,List.getLast?_cons_cons] using endEq

end
end Lamping.AG
namespace Lamping.AG
open Graph
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {s : Schema} {kept : K → Label signature}

def PathSite.cancellation_canonical_fronts
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    (route : List (Endpoint site.net)) :
    s.Frontier → List (Endpoint site.net) := by
  intro f
  cases f with
    | inl branch => exact site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::
        (route.dropLast++[site.net.wire (.inl ⟨.inr (.inr ()),.inl ()⟩)])
    | inr branch => exact site.net.wire (.inl ⟨.inr (.inr ()),.inr branch⟩)::
        ((reverseEdges route).dropLast++[site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)])

theorem PathSite.cancellation_canonical_crossing_with_routes
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    (cancel : IsCancellation s) :
    ∃ principal : SiteActionPrincipal site,
    ∀ (f : s.Frontier) {es : List (Endpoint site.net)} {a b : Context},
      Labelling site.net es a b → (∃ k,accessKind site.net es=some k) →
      es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr f))))) →
      ∃ rest,es=site.cancellation_canonical_fronts principal.edges f++site.outsideEnd (.inr (.inl (.inr (cancellationMate s f))))::rest ∧
        site.cancellation_canonical_fronts principal.edges f≠[] ∧Labelling site.net
          (site.outsideEnd (.inr (.inl (.inr (cancellationMate s f))))::rest) a b := by
  obtain ⟨route,routeHead,routeLast,turns⟩ := site.principal_route
  have reverseHead : (reverseEdges route).head?=some (.inl ⟨.inr (.inr ()),.inl ()⟩) := by
    simp only [reverseEdges,List.head?_map,List.head?_reverse,routeLast,Option.map_some,Pairing.involutive]
  have reverseLast : (reverseEdges route).getLast?=some (site.net.wire (.inl ⟨.inr (.inl ()),.inl ()⟩)) := by
    simp only [reverseEdges,List.getLast?_map,List.getLast?_reverse,routeHead,Option.map_some]
  have reverseTurns : ∀ e f,(e,f)∈(reverseEdges route).zip (reverseEdges route).tail →
      ∃ w d,site.net.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)) := by
    exact transparent_reverse_turns route turns
  refine ⟨⟨route,routeHead,routeLast,turns⟩,?_⟩
  cases cancel
  all_goals
    intro f es a b labels typed first
    cases f with
    | inl branch =>
      obtain ⟨q,rest,same,split,tail⟩ := site.cancel_fixed_prefix (by constructor) route routeHead routeLast turns branch labels typed first
      have sameBranch := eq_of_heq same
      subst q
      exact ⟨rest,by simpa only [PathSite.cancellation_canonical_fronts,List.cons_append,List.append_assoc,List.singleton_append] using split,by simp [PathSite.cancellation_canonical_fronts],tail⟩
    | inr branch =>
      obtain ⟨q,rest,same,split,tail⟩ := site.cancel_reverse_fixed_prefix (by constructor) (reverseEdges route) reverseHead reverseLast reverseTurns branch labels typed first
      have sameBranch := eq_of_heq same
      subst q
      exact ⟨rest,by simpa only [PathSite.cancellation_canonical_fronts,List.cons_append,List.append_assoc,List.singleton_append] using split,by simp [PathSite.cancellation_canonical_fronts],tail⟩

theorem PathSite.cancellation_canonical_crossing
    (site : PathSite s kept (B:=B) (W:=W) (V:=V))
    (cancel : IsCancellation s) :
    ∃ fronts : s.Frontier → List (Endpoint site.net),
    ∀ (f : s.Frontier) {es : List (Endpoint site.net)} {a b : Context},
      Labelling site.net es a b → (∃ k,accessKind site.net es=some k) →
      es.head?=some (site.net.wire (site.outsideEnd (.inr (.inl (.inr f))))) →
      ∃ rest,es=fronts f++site.outsideEnd (.inr (.inl (.inr (cancellationMate s f))))::rest ∧
        fronts f≠[] ∧Labelling site.net
          (site.outsideEnd (.inr (.inl (.inr (cancellationMate s f))))::rest) a b := by
  obtain ⟨principal,crossing⟩ := site.cancellation_canonical_crossing_with_routes cancel
  exact ⟨site.cancellation_canonical_fronts principal.edges,crossing⟩

end
end Lamping.AG
namespace Lamping.AG
open Graph
section
variable {s : Schema} {K B W V : Type} [FiniteNames K] [FiniteNames B]
  [FiniteNames W] [FiniteNames V] {kept : K → Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
private theorem canonical_outside_injective : Function.Injective site.outsideEnd := by
  intro e f same
  let split := fragmentEnd (B:=B) (W:=W) site.net.label (pathPartition s V)
  change split.invFun (.inl e)=split.invFun (.inl f) at same
  have mapped := congrArg split same
  simpa only [split.right_inv,Sum.inl.injEq] using mapped

private theorem canonical_outside_turn {e : Endpoint (cutFragment site.net (pathPartition s V) site.closed)}
    {f : Endpoint site.net} {a b : Context}
    (turn : LabelledTurn site.net (site.net.wire (site.outsideEnd e)) f a b) :
    (∃ next,f=site.outsideEnd next ∧
      LabelledTurn (cutFragment site.net (pathPartition s V) site.closed)
        ((cutFragment site.net (pathPartition s V) site.closed).wire e) next a b) ∨
    ∃ frontier,(cutFragment site.net (pathPartition s V) site.closed).wire e=
      .inr (.inl (.inr frontier)) := by
  rw [site.outsideEnd_wire] at turn
  generalize (cutFragment site.net (pathPartition s V) site.closed).wire e=endpoint at turn ⊢
  rcases endpoint with ⟨node,p⟩ | ((boundary | frontier) | ⟨vertex,direction⟩)
  · change LabelledTurn site.net (.inl ⟨.inl node,p⟩) f a b at turn
    obtain ⟨q,same,rule⟩ := turn.from_node (.inl node) p rfl
    exact Or.inl ⟨.inl ⟨node,q⟩,same,.node node p q rule⟩
  · change LabelledTurn site.net (.inr (.inl boundary)) f a b at turn
    cases turn
  · exact Or.inr ⟨frontier,rfl⟩
  · change LabelledTurn site.net (.inr (.inr (.inl vertex,direction))) f a b at turn
    cases turn
    exact Or.inl ⟨.inr (.inr (vertex,!direction)),rfl,.transparent vertex direction a⟩


/-- This relation uses one fixed actual prefix map. No reconstruction
uniqueness is assumed as a field. -/
def CanonicalCancellationResidual
    (fronts : s.Frontier → List (Endpoint site.net))
    (es : List (Endpoint site.reduce)) (old : List (Endpoint site.net)) : Prop := by
  cases s with
  | fanCancel i =>
    let c := cutFragment site.net (pathPartition (.fanCancel i) V) site.closed
    let r := (Schema.fanCancel i).right.net
    exact CanonicalWireResidual c r site.net site.outsideEnd fronts
      (es.map (plugEnd c.label r.label).invFun) old
  | croCancel i =>
    let c := cutFragment site.net (pathPartition (.croCancel i) V) site.closed
    let r := (Schema.croCancel i).right.net
    exact CanonicalWireResidual c r site.net site.outsideEnd fronts
      (es.map (plugEnd c.label r.label).invFun) old
  | braCancel i =>
    let c := cutFragment site.net (pathPartition (.braCancel i) V) site.closed
    let r := (Schema.braCancel i).right.net
    exact CanonicalWireResidual c r site.net site.outsideEnd fronts
      (es.map (plugEnd c.label r.label).invFun) old
  | _ => exact False

/-- Forget the fixed-route refinement, retaining the actual old residual. -/
theorem CanonicalCancellationResidual.erase (cancel : IsCancellation s)
    {fronts es old} (relation : CanonicalCancellationResidual site fronts es old) :
    CancellationResidual site es old := by
  cases cancel
  all_goals exact CanonicalWireResidual.erase _ _ _ _ _ relation
theorem CanonicalCancellationResidual.source_unique
    (cancel : IsCancellation s) {fronts es first second}
    (left : CanonicalCancellationResidual site fronts es first)
    (right : CanonicalCancellationResidual site fronts es second) : first=second := by
  cases cancel
  all_goals exact CanonicalWireResidual.source_unique _ _ _ _ _ left right

/-- One principal/reverse selection is shared by every existing source path.
The actual new labels and the canonical residual are conclusions. -/
theorem PathSite.cancellation_canonical_source_contraction_with_routes (cancel : IsCancellation s) :
    ∃ principal : SiteActionPrincipal site,
    ∀ {old : List (Endpoint site.net)} {a b : Context},
      Labelling site.net old a b → (∃ k,accessKind site.net old=some k) →
      ∀ (first last : Endpoint (cutFragment site.net (pathPartition s V) site.closed)),
      old.head?=some (site.outsideEnd first) → old.getLast?=some (site.outsideEnd last) →
      ∃ es,Labelling site.reduce es a b ∧CanonicalCancellationResidual site (site.cancellation_canonical_fronts principal.edges) es old ∧
        es.head?=some (plugLeft _ s.right.net first) ∧
        es.getLast?=some (plugLeft _ s.right.net last) := by
  obtain ⟨principal,crossing⟩ := site.cancellation_canonical_crossing_with_routes cancel
  let fronts := site.cancellation_canonical_fronts principal.edges
  refine ⟨principal,?_⟩
  intro old a b labels typed first last head finish
  let c := cutFragment site.net (pathPartition s V) site.closed
  let r := s.right.net
  cases cancel
  all_goals
    obtain ⟨raw,path,residual,start,endEq⟩ := Labelling.contract_canonical_typed_wire_source c r site.net
      site.outsideEnd fronts (canonical_outside_injective site) site.outsideEnd_wire
      (canonical_outside_turn site)
      (fun frontier {es} {input} {output} given actual ends => by
        have split := crossing frontier given actual ends
        cases frontier <;> exact split)
      labels typed first last head finish
    refine ⟨raw.map (plugEnd c.label r.label),(path.labelling c r).actual c r,?_,?_,?_⟩
    · change CanonicalWireResidual c r site.net site.outsideEnd fronts
        ((raw.map (plugEnd c.label r.label)).map (plugEnd c.label r.label).invFun) old
      simpa only [List.map_map,Function.comp_def,(plugEnd c.label r.label).left_inv,List.map_id_fun'] using residual
    · rw [List.head?_map,start]
      rfl
    · rw [List.getLast?_map,endEq]
      rfl

theorem PathSite.cancellation_canonical_source_contraction (cancel : IsCancellation s) :
    ∃ fronts : s.Frontier → List (Endpoint site.net),
    ∀ {old : List (Endpoint site.net)} {a b : Context},
      Labelling site.net old a b → (∃ k,accessKind site.net old=some k) →
      ∀ (first last : Endpoint (cutFragment site.net (pathPartition s V) site.closed)),
      old.head?=some (site.outsideEnd first) → old.getLast?=some (site.outsideEnd last) →
      ∃ es,Labelling site.reduce es a b ∧CanonicalCancellationResidual site fronts es old ∧
        es.head?=some (plugLeft _ s.right.net first) ∧
        es.getLast?=some (plugLeft _ s.right.net last) := by
  obtain ⟨principal,contract⟩ := site.cancellation_canonical_source_contraction_with_routes cancel
  exact ⟨site.cancellation_canonical_fronts principal.edges,contract⟩

end
end Lamping.AG
namespace Lamping.AG
open Graph
section
variable {K B F W N D V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames F]
  [FiniteNames W] [FiniteNames N] [FiniteNames D] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature Empty F Empty)
variable (g : Net signature N D V) (embed : Endpoint c → Endpoint g)
variable (fronts : F → List (Endpoint g))

theorem CanonicalWireResidual.head {raw old}
    (relation : CanonicalWireResidual c r g embed fronts raw old)
    {e : Endpoint c} (first : raw.head?=some (.inl e)) : old.head?=some (embed e) := by
  induction relation generalizing e with
  | single f => have same := Sum.inl.inj (Option.some.inj first); subst f; rfl
  | @outside f h tail old rest ih =>
    have same := Sum.inl.inj (Option.some.inj first); subst f; rfl
  | @through f h tail old start rest ih =>
    have same := Sum.inl.inj (Option.some.inj first); subst f
    cases frontEq : fronts h with
    | nil =>
      have endpoint : embed (.inr (.inl (.inr (wireBoundaryMate r h))))=embed e := by
        have endpoint := start
        simp only [frontEq,List.nil_append,List.head?_cons] at endpoint
        exact Option.some.inj endpoint
      simpa only [frontEq,List.nil_append,endpoint] using ih rfl
    | cons x xs => simpa only [frontEq,List.cons_append,List.head?_cons] using start

theorem CanonicalWireResidual.target_unique
    (injective : Function.Injective embed)
    (shape : ∀ f,∃ e x xs,fronts f=embed e::x::xs ∧∀ next,x≠embed next)
    (headInjective : ∀ f h,(fronts f).head?=(fronts h).head? → f=h)
    (first : CanonicalWireResidual c r g embed fronts raw old)
    (second : CanonicalWireResidual c r g embed fronts other right) (same : old=right) : raw=other := by
  induction first generalizing other right with
  | single e =>
    cases second with
    | single h =>
      have equal := injective (List.cons.inj same).1
      subst h
      rfl
    | @outside e' h tail old rest =>
      have head := rest.head c r g embed fronts rfl
      rw [←(List.cons.inj same).2] at head
      cases head
    | @through e' f tail old start rest =>
      obtain ⟨entry,inside,xs,frontEq,_⟩ := shape f
      rw [frontEq,List.cons_append] at same
      have wrong := (List.cons.inj same).2
      cases wrong
  | @outside e f tail old rest ih =>
    cases second with
    | single h =>
      have head := rest.head c r g embed fronts rfl
      rw [(List.cons.inj same).2] at head
      cases head
    | @outside e' f' tail' old' other =>
      have equal := injective (List.cons.inj same).1
      subst e'
      exact congrArg (Sum.inl e::·) (ih other (List.cons.inj same).2)
    | @through e' f' tail' old' start other =>
      obtain ⟨entry,inside,xs,frontEq,notOutside⟩ := shape f'
      rw [frontEq,List.cons_append] at same
      have head := rest.head c r g embed fronts rfl
      rw [(List.cons.inj same).2,List.cons_append,List.head?_cons] at head
      exact False.elim (notOutside f (Option.some.inj head))
  | @through e f tail old start rest ih =>
    cases second with
    | single h =>
      obtain ⟨entry,inside,xs,frontEq,_⟩ := shape f
      rw [frontEq,List.cons_append] at same
      have wrong := (List.cons.inj same).2
      cases wrong
    | @outside e' f' tail' old' other =>
      obtain ⟨entry,inside,xs,frontEq,notOutside⟩ := shape f
      rw [frontEq,List.cons_append] at same
      have head := other.head c r g embed fronts rfl
      rw [←(List.cons.inj same).2,List.cons_append,List.head?_cons] at head
      exact False.elim (notOutside f' (Option.some.inj head))
    | @through e' f' tail' old' otherStart other =>
      obtain ⟨entry,inside,xs,frontEq,_⟩ := shape f
      obtain ⟨entry',inside',ys,otherFront,_⟩ := shape f'
      have equalHeads : (fronts f).head?=(fronts f').head? := by
        have heads := congrArg List.head? same
        simpa only [frontEq,otherFront,List.cons_append,List.head?_cons] using heads
      have frontierEq := headInjective f f' equalHeads
      subst f'
      have nodeEq := injective (Option.some.inj (start.symm.trans otherStart))
      subst e'
      exact congrArg (fun suffix=>Sum.inl e::Sum.inr (.inr (.inl f))::suffix)
        (ih other (List.append_cancel_left same))

end
end Lamping.AG