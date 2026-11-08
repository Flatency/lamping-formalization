import Lamping.Lambda.LabelProtectedHeadCut
import Lamping.Lambda.LabelCanonicalInternality
namespace Lamping.Lambda.Labelled

/-- In a normal pointed run, protected inside/right-disjoint geometry forces
the whole run inside its head occurrence. A right final occurrence would
select a real right sibling and delete the head through the actual rules. -/
theorem normal_head_internal_of_right_geometry
    (head : BetaAt source p middle) (tail : ParallelHistory middle target) (ordinary : Atomic tail)
    (positive : 0<tail.length)
    (normal : ExtractionNormal (.of (.cons (singleContraction head) tail) (.cons head ordinary)))
    (geometry : ∀ q∈tail.derivation.paths,(∃ suffix,q=p++suffix) ∨
      (LeftOf p q ∧ DisjointPositions p q)) :
    Internal p (.cons (singleContraction head) tail) := by
  obtain ⟨beforeLast,q,pre,last,preAtomic,tailEq⟩ := ordinary.last positive
  let proper : ParallelHistory source beforeLast := .cons (singleContraction head) pre
  have properAtomic : Atomic proper := .cons head preAtomic
  have fullPaths : (ParallelHistory.cons (singleContraction head) tail).derivation.paths=
      (proper.append (.single (singleContraction last))).derivation.paths := by
    rw [tailEq]
    rfl
  have fullEq : ExtractionRun.of (.cons (singleContraction head) tail) (.cons head ordinary)=
      ExtractionRun.of (proper.append (.single (singleContraction last))) (properAtomic.append (.single last)) := by
    apply ExtractionRun.ext_paths
    exact fullPaths
  have properNormal : ExtractionNormal (.of (proper.append (.single (singleContraction last)))
      (properAtomic.append (.single last))) := by rw [←fullEq]; exact normal
  have earlierMember : ∀ r∈pre.derivation.paths,r∈tail.derivation.paths := by
    intro r member
    rw [tailEq]
    simp only [ParallelHistory.derivation_append,Derivation.append,ParallelHistory.single_derivation]
    change r∈pre.derivation.paths++[q]
    exact List.mem_append_left _ member
  have lastMember : q∈tail.derivation.paths := by
    rw [tailEq]
    simp only [ParallelHistory.derivation_append,Derivation.append,ParallelHistory.single_derivation]
    change q∈pre.derivation.paths++[q]
    exact List.mem_append_right _ List.mem_cons_self
  rcases geometry q lastMember with ⟨suffix,lastAt⟩ | ⟨lastRight,lastApart⟩
  · have localGeometry : ∀ r∈proper.derivation.paths,(∃ suffix,r=p++suffix) ∨ DisjointPositions r p := by
      intro r member
      change r∈p::pre.derivation.paths at member
      rcases List.mem_cons.mp member with first | later
      · exact .inl ⟨[],by simpa only [List.append_nil] using first⟩
      · rcases geometry r (earlierMember r later) with inside | ⟨_,apart⟩
        · exact .inl inside
        · exact .inr apart.symm
    have inside := normal_internal_of_geometry properAtomic last properNormal lastAt localGeometry
    intro r member
    exact inside r (fullPaths ▸ member)
  · obtain ⟨site,suffix,lastAt,headApart,siblingGeometry⟩ := lastRight.right_sibling lastApart
    have localGeometry : ∀ r∈proper.derivation.paths,(∃ suffix,r=site++suffix) ∨ DisjointPositions r site := by
      intro r member
      change r∈p::pre.derivation.paths at member
      rcases List.mem_cons.mp member with first | later
      · exact .inr (first ▸ headApart)
      · rcases geometry r (earlierMember r later) with ⟨suffix,inside⟩ | ⟨right,_⟩
        · exact .inr (inside ▸ headApart.descend_left suffix)
        · exact siblingGeometry r right
    have inside := normal_internal_of_geometry properAtomic last properNormal lastAt localGeometry
    have headMember : p∈(proper.append (.single (singleContraction last))).derivation.paths := by
      simp only [ParallelHistory.derivation_append,Derivation.append,ParallelHistory.single_derivation]
      change p∈(p::pre.derivation.paths)++[q]
      exact List.mem_append_left _ List.mem_cons_self
    exact False.elim (headApart.2 (inside p headMember))

/-- The protected-cut theorem is now consumed by actual extraction normality.
Every tail event, including its last contraction, has the visible recursive
avoidance premise; no internality or static component conclusion is supplied. -/
theorem RegionalHistory.normal_head_internal
    (regional : RegionalHistory (fun n => n≠a) qs u v) (head : StepAt p t u)
    (initial : INIT t) (degree : t.degreeAt p=some (Label.atom a))
    (tail : ParallelHistory u.erase v.erase) (ordinary : Atomic tail)
    (standard : Standard (.cons (singleContraction head.betaAt) tail))
    (paths : tail.derivation.paths=qs) (positive : 0<qs.length)
    (normal : ExtractionNormal (.of (.cons (singleContraction head.betaAt) tail) (.cons head.betaAt ordinary))) :
    Internal p (.cons (singleContraction head.betaAt) tail) := by
  have geometry := regional.head_tail_geometry head initial degree tail ordinary standard paths
  have tailPositive : 0<tail.length := by
    have length := congrArg List.length paths
    rw [ordinary.paths_length] at length
    omega
  exact normal_head_internal_of_right_geometry head.betaAt tail ordinary tailPositive normal
    (fun q member => geometry q (paths ▸ member))
end Lamping.Lambda.Labelled


