import Lamping.Lamping.TypedWireSourceContraction
import Lamping.Lamping.UnobservedPathWords
namespace Lamping.AG
open Graph
section
variable {K B F W N D V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames F]
  [FiniteNames W] [FiniteNames N] [FiniteNames D] [FiniteNames V]
variable (c : Net signature K (B⊕F) W) (r : Net signature Empty F Empty)
variable (g : Net signature N D V) (embed : Endpoint c → Endpoint g)

/-- A new finite residual recording the actual nonempty removed fronts and
absence of proper arrivals. This does not strengthen the old bare relation. -/
inductive UnobservedWireResidual : List (PlugSegment c r) → List (Endpoint g) → Prop where
  | single (e : Endpoint c) : UnobservedWireResidual [.inl e] [embed e]
  | outside {e f : Endpoint c} {tail old}
      (rest : UnobservedWireResidual (.inl f::tail) old) :
      UnobservedWireResidual (.inl e::.inl f::tail) (embed e::old)
  | through {e : Endpoint c} {f : F} {tail old} (front : List (Endpoint g))
      (start : (front++[embed (.inr (.inl (.inr (wireBoundaryMate r f))))]).head?=some (embed e))
      (nonempty : front≠[]) (unobserved : ∀ x∈front,accessKind g [x]=none)
      (rest : UnobservedWireResidual (.inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) old) :
      UnobservedWireResidual (.inl e::.inr (.inr (.inl f))::
        .inl (.inr (.inl (.inr (wireBoundaryMate r f))))::tail) (front++old)

theorem UnobservedWireResidual.erase {raw old}
    (relation : UnobservedWireResidual c r g embed raw old) : WireBlockResidual c r g embed raw old := by
  induction relation with
  | single e => exact .single e
  | outside rest ih => exact .outside ih
  | through front start nonempty unobserved rest ih => exact .through front start ih

theorem UnobservedWireResidual.head {raw old}
    (relation : UnobservedWireResidual c r g embed raw old) {e : Endpoint c}
    (first : raw.head?=some (.inl e)) : old.head?=some (embed e) := by
  induction relation generalizing e with
  | single f => have same := Sum.inl.inj (Option.some.inj first); subst f; rfl
  | @outside f h tail old rest ih =>
    have same := Sum.inl.inj (Option.some.inj first)
    subst f
    rfl
  | @through f h tail old front start nonempty unobserved rest ih =>
    have same := Sum.inl.inj (Option.some.inj first)
    subst f
    cases front with
    | nil => exact False.elim (nonempty rfl)
    | cons x front => simpa only [List.cons_append,List.head?_cons] using start

/-- The existing finite contraction algorithm also records these local
observation facts when they are proved for the actual selected fronts. -/
theorem Labelling.contract_unobserved_wire_source
    (embedInjective : Function.Injective embed)
    (wiring : ∀ e,g.wire (embed e)=embed (c.wire e))
    (outside : ∀ {e : Endpoint c} {f : Endpoint g} {a b : Context},
      LabelledTurn g (g.wire (embed e)) f a b →
      (∃ h,f=embed h ∧LabelledTurn c (c.wire e) h a b) ∨
      ∃ frontier,c.wire e=.inr (.inl (.inr frontier)))
    (crossing : ∀ (frontier : F) {es : List (Endpoint g)} {a b : Context},
      Labelling g es a b → (∃ k,accessKind g es=some k) →
      es.head?=some (g.wire (embed (.inr (.inl (.inr frontier))))) →
      ∃ front rest,es=front++embed (.inr (.inl (.inr (wireBoundaryMate r frontier))))::rest ∧
        front≠[] ∧(∀ e∈front,accessKind g [e]=none) ∧Labelling g (embed (.inr (.inl (.inr (wireBoundaryMate r frontier))))::rest) a b)
    {es : List (Endpoint g)} {a b : Context} (labels : Labelling g es a b)
    (typed : ∃ k,accessKind g es=some k)
    (first last : Endpoint c) (head : es.head?=some (embed first))
    (finish : es.getLast?=some (embed last)) :
    ∃ raw,WireExcursions c r raw a b ∧UnobservedWireResidual c r g embed raw es ∧
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
        obtain ⟨front,rest,split,frontNonempty,noProper,suffixLabels⟩ := crossing frontier
          (.cons turn remaining) typed (by simpa only [List.head?_cons] using congrArg some enters)
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
          cases front with
          | nil => exact False.elim (frontNonempty rfl)
          | cons x front => simpa only [split,List.cons_append,List.head?_cons] using head
        refine ⟨.inl first::.inr (.inr (.inl frontier))::.inl paired::post,.through arrival path,?_,rfl,?_⟩
        · rw [split]
          exact .through front blockHead frontNonempty noProper residual
        · simpa only [rawSplit,List.getLast?_cons_cons] using endEq
end
end Lamping.AG
