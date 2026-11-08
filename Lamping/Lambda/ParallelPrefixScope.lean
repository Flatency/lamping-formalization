import Lamping.Lambda.CreationContexts
namespace Lamping.Lambda

/-- Reflect an arbitrary actual complete development confined by its source
selection into a fixed subtree. Invalid selection names remain allowed. -/
theorem ParallelStep.prefix_scope
    (h : ParallelStep (G.map (fun q => pre++q)) t u)
    (hp : subtermAt t pre=some a) :
    ∃ b, ∃ k : ParallelStep G a b,
      subtermAt u pre=some b ∧ h.paths=k.paths.map (fun q => pre++q) := by
  induction pre generalizing t u G a with
  | nil =>
    simp only [subtermAt,Option.some.injEq] at hp
    subst a
    let k := h.reindex G (fun p => by simp)
    exact ⟨u,k,by cases u <;> rfl,by simp [k,ParallelStep.reindex]⟩
  | cons e pre ih =>
    have frame (C : SyntaxFrame) (b : Term)
        (h : ParallelStep (G.map (fun q => (C.edge::pre)++q)) (C.plug b) u)
        (hp : subtermAt (C.plug b) (C.edge::pre)=some a) :
        ∃ b', ∃ k : ParallelStep G a b',
          subtermAt u (C.edge::pre)=some b' ∧
          h.paths=k.paths.map (fun q => (C.edge::pre)++q) := by
      let h' := h.reindex ((G.map (fun q => pre++q)).map (C.edge::·))
        (fun p => by simp only [List.map_map,Function.comp_def,List.cons_append])
      obtain ⟨c,k,hu,paths⟩ := C.parallel_reflect h'
      subst u
      have localLookup : subtermAt b pre=some a := by
        change subtermAt (C.plug b) ([C.edge]++pre)=some a at hp
        simpa only [subtermAt_append,C.lookup,Option.bind_some] using hp
      obtain ⟨d,localStep,lookup,localPaths⟩ := ih k localLookup
      refine ⟨d,localStep,?_,?_⟩
      · change subtermAt (C.plug c) ([C.edge]++pre)=some d
        rw [subtermAt_append,C.lookup,Option.bind_some,lookup]
      · calc
          h.paths=k.paths.map (C.edge::·) := paths
          _=(localStep.paths.map (fun q => pre++q)).map (C.edge::·) := by rw [localPaths]
          _=localStep.paths.map (fun q => (C.edge::pre)++q) := by
            simp only [List.map_map,Function.comp_def,List.cons_append]
    cases t with
    | var i => cases e <;> simp [subtermAt] at hp
    | lam b =>
      cases e with
      | body => exact frame .body b h hp
      | fn => simp [subtermAt] at hp
      | arg => simp [subtermAt] at hp
    | app f b =>
      cases e with
      | fn => exact frame (.fn b) f h hp
      | arg => exact frame (.arg f) b h hp
      | body => simp [subtermAt] at hp

/-- Source selection confinement implies actual schedule confinement,
including arbitrary invalid names and repetitions in the selection list. -/
theorem ParallelStep.paths_scope (h : ParallelStep F t u)
    (scope : ∀ q∈F, ∃ s, q=pre++s) (hp : subtermAt t pre=some a) :
    ∀ q∈h.paths, ∃ s, q=pre++s := by
  have rebuild (xs : List Path) (hs : ∀ q∈xs, ∃ s, q=pre++s) :
      ((xs.map (List.drop pre.length)).map (fun q => pre++q))=xs := by
    induction xs with
    | nil => rfl
    | cons q qs ih =>
      obtain ⟨tail,hq⟩ := hs q (by simp)
      have rest := ih (fun z hz => hs z (by simp [hz]))
      simp only [List.map_cons]
      simp only [hq,List.drop_left,rest]
  have selectionMap := rebuild F scope
  let narrowed := h.reindex ((F.map (List.drop pre.length)).map (fun q => pre++q))
    (fun q => by rw [selectionMap])
  obtain ⟨b,k,_,paths⟩ := narrowed.prefix_scope hp
  intro q hq
  have hq' : q∈narrowed.paths := hq
  rw [paths] at hq'
  obtain ⟨s,_,hs⟩ := List.mem_map.mp hq'
  exact ⟨s,hs.symm⟩

end Lamping.Lambda
