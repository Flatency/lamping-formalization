import Lamping.Lamping.ActualChainLabelConverse
import Lamping.Lamping.ActualUnsafeMarkerLeaves
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
variable {t : LTerm}

private theorem actual_reader_proper (reading : PrerequisiteReadsDirected t reader edge d) :
    ProperAt t reader := by
  rcases reading.1 with ⟨stamp,fn,arg,lookup,_⟩ |⟨stamp,body,lookup,_⟩
  · exact Or.inl ⟨stamp,fn,arg,lookup⟩
  · exact Or.inr ⟨stamp,body,lookup⟩

private theorem proper_target_path {vertex : ProperPosition t}
    (proper : ProperAt t p) (atVertex : Target t p (some vertex)) : vertex.val=p := by
  let actual : ProperPosition t:=⟨p,proper⟩
  have eq : vertex=actual:=Option.some.inj (Target.unique atVertex (Or.inl rfl))
  exact congrArg Subtype.val eq

private theorem source_parent_target {vertex : ProperPosition t}
    (actual : Source t (parent++[step]) (some vertex)) : Target t parent (some vertex) := by
  obtain ⟨other,child,port,split,_,_⟩:=actual
  have lengths:=congrArg List.length split
  simp only [List.length_append,List.length_singleton] at lengths
  have equal : parent=vertex.val:=List.append_inj_left split (by omega)
  exact Or.inl equal

/-- Locate THAT real prefix's next directed reading inside an anchored signed
walk. Binder jumps consume no edge. The redex singleton direction is fixed by
its actual start, never by the edge label or edge coordinate alone. -/
theorem PrerequisitePrefix.signed_slot
    (segment : PrerequisitePrefix t start before reader)
    (reading : PrerequisiteReadsDirected t reader edge forward)
    {first : ProperPosition t}
    (walk : SignedProperWalk t first (before++edge::after) signs vertices)
    (endpoint : Target t start (some first)) :
    ∃actualReader : ProperPosition t,actualReader.val=reader ∧
      vertices[before.length]?=some actualReader ∧signs[before.length]?=some forward := by
  induction segment generalizing first signs vertices with
  | refl =>
    cases walk with
    | cons actualReading step tail =>
      have path:=proper_target_path (actual_reader_proper reading) endpoint
      have alignedReading : PrerequisiteReadsDirected t first.val edge forward:=by
        rw [path];exact reading
      have sameKind := alignedReading.proper_kind
      have direction:=actualReading.proper_kind.unique sameKind
      exact ⟨_,path,rfl,by simpa only [List.length_nil,List.getElem?_cons_zero] using congrArg some direction⟩
  | @app p stamp fn arg before finish lookup notLambda segment ih =>
    have path:=proper_target_path (Or.inl ⟨stamp,fn,arg,lookup⟩) endpoint
    cases walk with
    | @cons a b edge edges ss vs d actualReading step tail =>
      have actualKind : ProperKind t first true := by
        change ∃stamp fn arg,t.subterm first.val=some (.app stamp fn arg)
        rw [path];exact ⟨stamp,fn,arg,lookup⟩
      have direction:=actualReading.proper_kind.unique actualKind
      subst d
      obtain ⟨actualReader,atReader,atVertex,atSign⟩:=ih reading tail step.2
      exact ⟨actualReader,atReader,by simpa only [List.length_cons,List.getElem?_cons_succ] using atVertex,
        by simpa only [List.length_cons,List.getElem?_cons_succ] using atSign⟩
  | @lam parent child stamp body before finish lookup notFunction segment ih =>
    have path:=proper_target_path (Or.inr ⟨stamp,body,lookup⟩) endpoint
    cases walk with
    | @cons a b edge edges ss vs d actualReading step tail =>
      have actualKind : ProperKind t first false := by
        change ∃stamp body,t.subterm first.val=some (.lam stamp body)
        rw [path];exact ⟨stamp,body,lookup⟩
      have direction:=actualReading.proper_kind.unique actualKind
      subst d
      obtain ⟨actualReader,atReader,atVertex,atSign⟩:=ih reading tail (source_parent_target step.2)
      exact ⟨actualReader,atReader,by simpa only [List.length_cons,List.getElem?_cons_succ] using atVertex,
        by simpa only [List.length_cons,List.getElem?_cons_succ] using atSign⟩
  | @var leaf stamp index parent origin body rest before finish lookup binder split depth segment ih =>
    let actual : ProperPosition t:=⟨parent,Or.inr ⟨origin,body,binder⟩⟩
    have actualTarget : Target t leaf (some actual):=
      Or.inr ⟨stamp,index,origin,body,rest,lookup,binder,split,depth⟩
    have equal : first=actual:=Option.some.inj (Target.unique endpoint actualTarget)
    have binderTarget : Target t parent (some first):=by rw [equal];exact Or.inl rfl
    exact ih reading walk binderTarget

/-- A genuine complete chain chooses its own anchored signed walk. Every
returned slot still refers to the supplied actual prefix/reader/read. -/
theorem PrerequisiteChain.signed_slot
    (chain : PrerequisiteChain t start edges)
    (split : edges=before++edge::after)
    (segment : PrerequisitePrefix t start before reader)
    (reading : PrerequisiteReadsDirected t reader edge forward) :
    ∃first signs vertices,Target t start (some first) ∧
      SignedProperWalk t first edges signs vertices ∧
      ∃actualReader : ProperPosition t,actualReader.val=reader ∧
        vertices[before.length]?=some actualReader ∧signs[before.length]?=some forward := by
  obtain ⟨first,signs,vertices,endpoint,walk⟩:=chain.signed_path
  have aligned : SignedProperWalk t first (before++edge::after) signs vertices:=split ▸ walk
  obtain ⟨actualReader,path,atReader,atSign⟩:=segment.signed_slot reading aligned endpoint
  exact ⟨first,signs,vertices,endpoint,walk,actualReader,path,atReader,atSign⟩
end Lamping.Lambda.Labelled

namespace Lamping.AG
open Lambda Lambda.Labelled SyntaxIncidence
variable {source current : LTerm}

/-- Reuse an arbitrary supplied actual signed walk of THIS whole chain;
no fresh orientation, desired cut or arbitrary redex reading is selected. -/
theorem ActualUnsafeMarkerCut.signed_slot
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges)
    {first : ProperPosition current}
    (walk : SignedProperWalk current first edges signs vertices)
    (endpoint : Target current start (some first)) :
    ∃actualReader : ProperPosition current,actualReader.val=cut.reader ∧
      vertices[cut.before.length]?=some actualReader ∧signs[cut.before.length]?=some cut.forward := by
  exact cut.segment.signed_slot cut.reading (cut.split ▸ walk) endpoint

/-- The cut's actual prefix and remaining successful chain internally supply
its complete chain and anchored signed walk, including zero binder jumps. -/
theorem ActualUnsafeMarkerCut.signed_path_slot
    (cut : ActualUnsafeMarkerCut F ps source current degree start edges) :
    ∃first signs vertices,Target current start (some first) ∧
      SignedProperWalk current first edges signs vertices ∧
      ∃actualReader : ProperPosition current,actualReader.val=cut.reader ∧
        vertices[cut.before.length]?=some actualReader ∧signs[cut.before.length]?=some cut.forward := by
  have chain : PrerequisiteChain current start edges:=by rw [cut.split];exact cut.segment.close cut.remaining
  exact chain.signed_slot cut.split cut.segment cut.reading
end Lamping.AG
