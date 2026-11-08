import Lamping.Lamping.ComputedControlSchemaTable

namespace Lamping.AG.ExposureScheduling

/-- With the genuine initial-reader index bound, the SAME computation selects
the lower right control against APP and reverses the physical corridor. -/
theorem computeControlPairSchema_initial_reader {control : Op} {appIndex controlIndex : Nat}
    (kind : control=.fan ∨control=.cro ∨control=.bra) (lower : controlIndex<appIndex) :
    ∃ schema,computeControlPairSchema .app control appIndex controlIndex=some (schema,true) ∧
      OrientedControlSchemaFits (schema,true) .app control appIndex controlIndex := by
  have unequal : appIndex≠controlIndex := Nat.ne_of_gt lower
  have notLower : ¬appIndex<controlIndex := Nat.not_lt.mpr (Nat.le_of_lt lower)
  rcases kind with same|same|same <;> subst control
  · refine ⟨.fanAction .app controlIndex appIndex lower,?_,⟨rfl,rfl,rfl,rfl⟩⟩
    unfold computeControlPairSchema
    rw [if_neg unequal,if_neg notLower]
    change (if h : controlIndex<appIndex then some (Schema.fanAction .app controlIndex appIndex h)
      else none).map (fun schema => (schema,true))=some (Schema.fanAction .app controlIndex appIndex lower,true)
    simp only [dif_pos lower,Option.map_some]
  · refine ⟨.croAction .app controlIndex appIndex lower,?_,⟨rfl,rfl,rfl,rfl⟩⟩
    unfold computeControlPairSchema
    rw [if_neg unequal,if_neg notLower]
    change (if h : controlIndex<appIndex then some (Schema.croAction .app controlIndex appIndex h)
      else none).map (fun schema => (schema,true))=some (Schema.croAction .app controlIndex appIndex lower,true)
    simp only [dif_pos lower,Option.map_some]
  · refine ⟨.braAction .app controlIndex appIndex lower,?_,⟨rfl,rfl,rfl,rfl⟩⟩
    unfold computeControlPairSchema
    rw [if_neg unequal,if_neg notLower]
    change (if h : controlIndex<appIndex then some (Schema.braAction .app controlIndex appIndex h)
      else none).map (fun schema => (schema,true))=some (Schema.braAction .app controlIndex appIndex lower,true)
    simp only [dif_pos lower,Option.map_some]

/-- With the genuine terminal-writer bound, the SAME computation selects the
lower left control against lambda in the original physical orientation. -/
theorem computeControlPairSchema_terminal_writer {control : Op} {controlIndex lamIndex : Nat}
    (kind : control=.fan ∨control=.cro ∨control=.bra) (lower : controlIndex<lamIndex) :
    ∃ schema,computeControlPairSchema control .lam controlIndex lamIndex=some (schema,false) ∧
      OrientedControlSchemaFits (schema,false) control .lam controlIndex lamIndex := by
  have unequal : controlIndex≠lamIndex := Nat.ne_of_lt lower
  rcases kind with same|same|same <;> subst control
  · refine ⟨.fanAction .lam controlIndex lamIndex lower,?_,⟨rfl,rfl,rfl,rfl⟩⟩
    unfold computeControlPairSchema
    rw [if_neg unequal,if_pos lower]
    change (if h : controlIndex<lamIndex then some (Schema.fanAction .lam controlIndex lamIndex h)
      else none).map (fun schema => (schema,false))=some (Schema.fanAction .lam controlIndex lamIndex lower,false)
    simp only [dif_pos lower,Option.map_some]
  · refine ⟨.croAction .lam controlIndex lamIndex lower,?_,⟨rfl,rfl,rfl,rfl⟩⟩
    unfold computeControlPairSchema
    rw [if_neg unequal,if_pos lower]
    change (if h : controlIndex<lamIndex then some (Schema.croAction .lam controlIndex lamIndex h)
      else none).map (fun schema => (schema,false))=some (Schema.croAction .lam controlIndex lamIndex lower,false)
    simp only [dif_pos lower,Option.map_some]
  · refine ⟨.braAction .lam controlIndex lamIndex lower,?_,⟨rfl,rfl,rfl,rfl⟩⟩
    unfold computeControlPairSchema
    rw [if_neg unequal,if_pos lower]
    change (if h : controlIndex<lamIndex then some (Schema.braAction .lam controlIndex lamIndex h)
      else none).map (fun schema => (schema,false))=some (Schema.braAction .lam controlIndex lamIndex lower,false)
    simp only [dif_pos lower,Option.map_some]
end Lamping.AG.ExposureScheduling
