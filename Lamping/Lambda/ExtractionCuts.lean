import Lamping.Lambda.ExtractionIndex
namespace Lamping.Lambda

/-- A deletion at a positive index of a run beginning with R belongs to
 its ordinary tail. The actual target retains precisely that first R. -/
theorem ExtractionAt.uncons (R : BetaAt t p u) (tail : ExtractionRun u)
    (h : ExtractionAt (n + 1) (tail.prepend (.single (singleContraction R)) (.single R)) s) :
    ∃ result : ExtractionRun u, ExtractionAt n tail result ∧
      s = result.prepend (.single (singleContraction R)) (.single R) := by
  obtain ⟨a,b,q,pre,ha,S,rest,result,root,source,target,index⟩ := h
  cases tail with
  | mk endpoint history hh =>
    cases rest with
    | mk endpoint' suffix hs =>
      have targets : endpoint = endpoint' := congrArg ExtractionRun.target source
      cases targets
      have paths := congrArg (fun r => r.history.derivation.paths) source
      have whole : (ParallelHistory.single (singleContraction R)).append history =
          pre.append (.cons (singleContraction S) suffix) :=
        ((Atomic.single R).append hh).paths_injective (ha.append (.cons S hs)) paths
      have bound : (ParallelHistory.single (singleContraction R)).length ≤ pre.length := by
        change 1 ≤ pre.length
        omega
      obtain ⟨bridge,hbridge,preEq,tailEq⟩ := (Atomic.single R).prefix_comparable ha hh
        (.cons S hs) whole bound
      have bridgeLength : bridge.length = n := by
        have len := congrArg ParallelHistory.length preEq
        simp only [ParallelHistory.length_append, ParallelHistory.single, ParallelHistory.length] at len
        omega
      let reduced := result.prepend bridge hbridge
      refine ⟨reduced, ?_, ?_⟩
      · refine ⟨a,b,q,bridge,hbridge,S,.of suffix hs,result,root,?_,rfl,bridgeLength⟩
        apply ExtractionRun.ext_paths
        exact congrArg (fun h => h.derivation.paths) tailEq
      · rw [target]
        apply ExtractionRun.ext_paths
        have prefixPaths := congrArg (fun h => h.derivation.paths) preEq
        simp only [ParallelHistory.derivation_append, Derivation.append] at prefixPaths
        simp only [ExtractionRun.prepend, ExtractionRun.of, reduced,
          ParallelHistory.derivation_append, Derivation.append]
        rw [prefixPaths, List.append_assoc]

/-- Strip any actual ordinary common prefix lying before a deletion index.
 This is source/target factorization, not closure under a right suffix. -/
theorem ExtractionAt.strip_prefix (pre : ParallelHistory t u) (ha : Atomic pre)
    (tail : ExtractionRun u)
    (h : ExtractionAt (pre.length + n) (tail.prepend pre ha) s) :
    ∃ result : ExtractionRun u, ExtractionAt n tail result ∧ s = result.prepend pre ha := by
  induction ha generalizing n with
  | nil =>
    refine ⟨s,?_,rfl⟩
    simpa only [ParallelHistory.length, Nat.zero_add] using h
  | @cons t p v u rest S hrest ih =>
    have head : ExtractionAt (rest.length + n + 1)
        ((tail.prepend rest hrest).prepend (.single (singleContraction S)) (.single S)) s := by
      have count : (ParallelHistory.cons (singleContraction S) rest).length + n = rest.length + n + 1 := by
        change 1 + rest.length + n = rest.length + n + 1
        omega
      rw [← count]
      exact h
    obtain ⟨middle, hm, hs⟩ := head.uncons S (tail.prepend rest hrest)
    obtain ⟨result, hr, he⟩ := ih tail hm
    refine ⟨result,hr,?_⟩
    rw [hs,he]
    rfl

/-- Any two strictly ordered deletion sites in a common actual source can
 be reduced to a root deletion versus an indexed extraction in its tail.
 The common prefix and the retained first contraction are both reconstructed. -/
theorem ExtractionAt.strict_fork_factor {i j : Nat} {r s s' : ExtractionRun M}
    (h : ExtractionAt i r s) (k : ExtractionAt j r s') (earlier : i < j) :
    ∃ (t u : Term) (p : Path) (pre : ParallelHistory M t) (ha : Atomic pre)
      (R : BetaAt t p u) (tail : ExtractionRun u) (result : ExtractionRun t)
      (other : ExtractionRun u), RootExtraction R tail result ∧
      ExtractionAt (j - i - 1) tail other ∧
      r = (ExtractionRun.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic)).prepend pre ha ∧
      s = result.prepend pre ha ∧
      s' = (other.prepend (.single (singleContraction R)) (.single R)).prepend pre ha := by
  obtain ⟨t,u,p,pre,ha,R,tail,result,root,source,target,index⟩ := h
  rw [source] at k
  have count : j = pre.length + (j - i) := by omega
  rw [count] at k
  obtain ⟨middle,hm,hs'⟩ := ExtractionAt.strip_prefix pre ha
    (.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic)) k
  have successor : j - i = (j - i - 1) + 1 := by omega
  rw [successor] at hm
  obtain ⟨other,ho,he⟩ := hm.uncons R tail
  exact ⟨t,u,p,pre,ha,R,tail,result,other,root,ho,source,target,
    hs'.trans (congrArg (ExtractionRun.prepend pre ha) he)⟩

end Lamping.Lambda
