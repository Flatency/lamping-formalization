import Lamping.Lamping.InitialOriginalWordMarkers
import Init.Data.List.Lemmas

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- A finite-list support calculation by ORDINAL, with empty selected values
and repeated list values allowed. -/
theorem flatMap_unique_ordinal {X Y : Type} (es : List X) (f : X → List Y)
    (k : Fin es.length) (others : ∀ j : Fin es.length,j≠k → f es[j]=[]) :
    es.flatMap f=f es[k] := by
  induction es with
  | nil => exact Fin.elim0 k
  | cons x xs ih =>
    rcases k with ⟨k,bound⟩
    cases k with
    | zero =>
      have empty : xs.flatMap f=[] := List.flatMap_eq_nil_iff.mpr (by
        intro y member
        obtain ⟨j,hj,atIndex⟩ := List.getElem_of_mem member
        have zero := others (Fin.succ ⟨j,hj⟩) (by
          intro same
          have values := congrArg Fin.val same
          change j+1=0 at values
          omega)
        change f (xs[j]'hj)=[] at zero
        rw [atIndex] at zero
        exact zero)
      change f x++xs.flatMap f=f x
      rw [empty,List.append_nil]
    | succ k =>
      let selected : Fin xs.length := ⟨k,by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using bound⟩
      have headZero := others ⟨0,by simp⟩ (by
        intro same
        have values := congrArg Fin.val same
        change 0=k+1 at values
        omega)
      change f x=[] at headZero
      have tailZero : ∀ j : Fin xs.length,j≠selected → f xs[j]=[] := by
        intro j different
        have zero := others j.succ (by
          intro same
          apply different
          apply Fin.ext
          change j.val=k
          have values := congrArg Fin.val same
          change j.val+1=k+1 at values
          omega)
        exact zero
      have reduced := ih selected tailZero
      change f x++xs.flatMap f=f xs[selected]
      rw [headZero,List.nil_append,reduced]

/-- The actual original root boundary supplies headNoInput internally.
Every literal suffix endpoint therefore kills its negative seed factor. -/
theorem OccurrenceFragment.initial_negative_factors_given_assignment
    {original : LTerm} {level : Nat} {position : Path}
    (fragment : OccurrenceFragment original (encode level original.erase).net (.inl ()) position)
    (addr : Addressing (encode level original.erase).net (boundaryAddressAt []))
    {a b : Context}
    (whole : Labelling (encode level original.erase).net fragment.fragment.access.val a b) :
    ∀ i : Fin fragment.fragment.segments.length,
      initialAtomAddress addr.nodes fragment.fragment.segments[i]=none ∧
      initialOriginalEntry original level addr
        ((encode level original.erase).net.wire fragment.fragment.segments[i])=[] := by
  have initial := encode_root_initial original.erase level fragment.fragment.access.val
    fragment.fragment.access.property.2.1 whole
  have noInput := initial.no_initial_inputs addr.nodes (by
    intro e head
    have same : e=.inr (.inl (.inl ())) :=
      Option.some.inj (head.symm.trans fragment.fragment.access.property.2.1)
    subst e
    rfl)
  intro i
  have member : fragment.fragment.segments[i]∈fragment.fragment.segments :=
    List.mem_iff_getElem.mpr ⟨i.val,i.isLt,rfl⟩
  have wholeMember : fragment.fragment.segments[i]∈fragment.fragment.access.val := by
    rw [fragment.fragment.literal]
    exact List.mem_append.mpr (Or.inr member)
  obtain ⟨j,hj,atIndex⟩ := List.getElem_of_mem wholeMember
  have noAtIndex := noInput ⟨j,hj⟩
  change initialAtomAddress addr.nodes (fragment.fragment.access.val[j]'hj)=none at noAtIndex
  rw [atIndex] at noAtIndex
  refine ⟨noAtIndex,?_⟩
  unfold initialOriginalEntry
  rw [Pairing.involutive,noAtIndex]

/-- Whole original physical-word fold, for arbitrary actual Addressing and
the given original whole assignment. The unique geometric ordinal and actual
occurrence lookup supply the selected word, which need not be nonempty. -/
theorem OccurrenceFragment.initial_original_word_given_assignment
    {original : LTerm} {level : Nat} {position : Path}
    (fragment : OccurrenceFragment original (encode level original.erase).net (.inl ()) position)
    (addr : Addressing (encode level original.erase).net (boundaryAddressAt []))
    {a b : Context}
    (whole : Labelling (encode level original.erase).net fragment.fragment.access.val a b) :
    physicalOriginalWord (initialOriginalWeights original level addr) fragment.fragment.segments =
      fragment.term.label.edgeWord := by
  have negative := fragment.initial_negative_factors_given_assignment addr whole
  obtain ⟨_middle,_prefixEvidence,_initial,i,marked,unique⟩ :=
    fragment.initial_unique_marker_given_assignment addr whole
  have selected : initialOriginalWeights original level addr fragment.fragment.segments[i]=
      fragment.term.label.edgeWord := by
    unfold initialOriginalWeights
    rw [(negative i).2]
    change initialOriginalEntry original level addr fragment.fragment.segments[i]++[]=fragment.term.label.edgeWord
    rw [List.append_nil]
    unfold initialOriginalEntry
    unfold InitialMarkerAt at marked
    simp only [marked,fragment.occurrence.lookup]
  have others : ∀ j : Fin fragment.fragment.segments.length,j≠i →
      initialOriginalWeights original level addr fragment.fragment.segments[j]=[] := by
    intro j different
    have noMarker : initialAtomAddress addr.nodes
        ((encode level original.erase).net.wire fragment.fragment.segments[j])=none := by
      cases phase : initialAtomAddress addr.nodes
          ((encode level original.erase).net.wire fragment.fragment.segments[j]) with
      | none => rfl
      | some p => exact False.elim (different (unique j p phase).1)
    unfold initialOriginalWeights
    rw [(negative j).2]
    change initialOriginalEntry original level addr fragment.fragment.segments[j]++[]=[]
    rw [List.append_nil]
    unfold initialOriginalEntry
    rw [noMarker]
  have folded := flatMap_unique_ordinal fragment.fragment.segments
    (initialOriginalWeights original level addr) i others
  exact folded.trans selected

#print axioms flatMap_unique_ordinal
#print axioms OccurrenceFragment.initial_negative_factors_given_assignment
#print axioms OccurrenceFragment.initial_original_word_given_assignment
end Lamping.AG
