import Lamping.Lambda.RootTailPeak
import Lamping.Lambda.ExtractionCuts
namespace Lamping.Lambda

theorem ExtractionAt.strict_peak_join (h : ExtractionAt i r s)
    (k : ExtractionAt j r s') (earlier : i<j) : ExtractionJoin s s' := by
  obtain ⟨t,u,p,pre,ha,R,tail,result,other,root,later,_,target,target'⟩ :=
    h.strict_fork_factor k earlier
  rw [target,target']
  exact (root.tail_join later.step).prepend pre ha

/-- The actual four-rule extraction relation is locally confluent. Equal
 indices give identical targets; unequal indices use the full root/tail
 critical-pair matrix after reconstructing the common ordinary prefix. -/
theorem extraction_locally_confluent (m : Term) : ExtractionLocallyConfluent m := by
  intro r s s' h k
  obtain ⟨i,hi⟩ := h.has_index
  obtain ⟨j,hj⟩ := k.has_index
  rcases Nat.lt_trichotomy i j with earlier | same | later
  · exact hi.strict_peak_join hj earlier
  · cases same
    exact hi.peak_join hj
  · obtain ⟨common,left,right⟩ := hj.strict_peak_join hi later
    exact ⟨common,right,left⟩

/-- Church--Rosser for the implemented original four extraction rules,
 derived from the proved critical pairs and actual length termination. -/
theorem extraction_church_rosser (m : Term) : ExtractionConfluent m :=
  extraction_newman (extraction_locally_confluent m)

theorem extraction_normal_unique {r s t : ExtractionRun m}
    (h : Extraction r s) (k : Extraction r t)
    (hs : ExtractionNormal s) (ht : ExtractionNormal t) : s=t :=
  extraction_normal_unique_of_local_confluence (extraction_locally_confluent m) h k hs ht

end Lamping.Lambda
