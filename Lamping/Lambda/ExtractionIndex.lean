import Lamping.Lambda.ExtractionAtRoot
namespace Lamping.Lambda

/-- The original step with its actual ordinary deletion index retained.
 RootExtraction contains exactly the four generators, and both full runs
 are equalities of actual histories after their common prefix is restored. -/
def ExtractionAt (n : Nat) (r s : ExtractionRun m) : Prop :=
  ∃ (t u : Term) (p : Path) (pre : ParallelHistory m t) (ha : Atomic pre)
    (R : BetaAt t p u) (tail : ExtractionRun u) (result : ExtractionRun t),
    RootExtraction R tail result ∧
    r = (ExtractionRun.of (.cons (singleContraction R) tail.history) (.cons R tail.atomic)).prepend pre ha ∧
    s = result.prepend pre ha ∧ pre.length = n

theorem ExtractionAt.step (h : ExtractionAt n r s) : ExtractionStep r s := by
  obtain ⟨t,u,p,pre,ha,R,tail,result,root,source,target,index⟩ := h
  rw [source,target]
  exact root.prepend pre ha

theorem ExtractionStep.has_index (h : ExtractionStep r s) : ∃ n, ExtractionAt n r s := by
  obtain ⟨t,u,p,pre,ha,R,tail,result,root,source,target⟩ := h.root_factor
  exact ⟨pre.length,t,u,p,pre,ha,R,tail,result,root,source,target,rfl⟩

theorem ExtractionStep.indexed_iff : ExtractionStep r s ↔ ∃ n, ExtractionAt n r s :=
  ⟨ExtractionStep.has_index, fun ⟨_,h⟩ => h.step⟩

/-- The full same-index peak of the original relation has identical targets.
 Prefix and last-redex implementations are reconstructed from the common
 actual source, not supplied as a normalized square. -/
theorem ExtractionAt.target_unique (h : ExtractionAt n r s) (k : ExtractionAt n r s') : s = s' := by
  obtain ⟨t,u,p,pre,ha,R,tail,result,root,source,target,index⟩ := h
  obtain ⟨t',u',p',pre',ha',R',tail',result',root',source',target',index'⟩ := k
  rw [target,target']
  exact RootExtraction.same_index_target_unique pre ha pre' ha' R R' tail tail' result result'
    root root' (source.symm.trans source') (index.trans index'.symm)

theorem ExtractionAt.peak_join (h : ExtractionAt n r s) (k : ExtractionAt n r s') :
    ExtractionJoin s s' := by
  cases h.target_unique k
  exact ⟨s,.refl _,.refl _⟩

end Lamping.Lambda
