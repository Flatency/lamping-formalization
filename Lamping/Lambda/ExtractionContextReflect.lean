import Lamping.Lambda.ProjectionContextReflect
import Lamping.Lambda.ExtractionInternal
import Lamping.Lambda.ExtractionAtRoot
import Lamping.Lambda.ProjectionSingletonSelection
namespace Lamping.Lambda
namespace SyntaxContext

theorem liftRun_injective (C : SyntaxContext) {t : Term} :
    Function.Injective (C.liftRun (t:=t)) := by
  intro r s equal
  apply ExtractionRun.ext_paths
  have mapped := congrArg (fun r => r.history.derivation.paths) equal
  change (C.liftRun r).history.derivation.paths=(C.liftRun s).history.derivation.paths at mapped
  rw [C.liftRun_paths,C.liftRun_paths] at mapped
  have dropped := congrArg (List.map (List.drop C.path.length)) mapped
  simpa only [List.map_map,Function.comp_def,List.drop_left,List.map_id_fun'] using dropped

theorem liftRun_internal (C : SyntaxContext) (r : ExtractionRun t) :
    Internal C.path (C.liftRun r).history := by
  intro q hq
  rw [C.liftRun_paths] at hq
  obtain ⟨p,_,he⟩ := List.mem_map.mp hq
  exact ⟨p,he.symm⟩

theorem reflectRun (C : SyntaxContext) (r : ExtractionRun (C.plug t))
    (inside : Internal C.path r.history) :
    ∃ s : ExtractionRun t, r=C.liftRun s := by
  obtain ⟨b,h,ordinary,_,_,paths⟩ := C.reflectHistory r.history r.atomic inside
  refine ⟨.of h ordinary,?_⟩
  apply ExtractionRun.ext_paths
  rw [C.liftRun_paths]
  exact paths

/-- The local shape of an arbitrary extraction successor is recovered from
actual internality; this is only a representation lemma, not step reflection. -/
theorem reflectSuccessorRun (C : SyntaxContext) {r : ExtractionRun t}
    {s : ExtractionRun (C.plug t)} (step : ExtractionStep (C.liftRun r) s) :
    ∃ q, s=C.liftRun q :=
  C.reflectRun s (step.internal (C.liftRun_internal r))

theorem reflectBeta (C : SyntaxContext) (global : BetaAt (C.plug t) (C.path++p) U) :
    ∃ u, BetaAt t p u ∧ U=C.plug u := by
  obtain ⟨u,inner,_,_⟩ := global.prefix_reflect (C.lookup t)
  exact ⟨u,inner,global.unique (C.liftBeta inner)⟩

theorem internal_lift_iff (C : SyntaxContext) (h : ParallelHistory t u) :
    Internal (C.path++site) (C.liftHistory h) ↔ Internal site h := by
  constructor
  · intro inside p hp
    have member : C.path++p∈(C.liftHistory h).derivation.paths := by
      rw [C.liftHistory_paths]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    obtain ⟨q,hq⟩ := inside (C.path++p) member
    exact ⟨q,List.append_cancel_left (by simpa only [List.append_assoc] using hq)⟩
  · exact C.liftHistory_internal

theorem disjoint_reflect (C : SyntaxContext)
    (apart : DisjointPositions (C.path++p) (C.path++q)) : DisjointPositions p q := by
  constructor
  · rintro ⟨tail,he⟩
    exact apart.1 ⟨tail,by rw [he,List.append_assoc]⟩
  · rintro ⟨tail,he⟩
    exact apart.2 ⟨tail,by rw [he,List.append_assoc]⟩

/-- A nonempty disjoint extraction region intersecting the hole lies inside
the hole. Its site cannot be an ancestor of the hole, since that would also
contain the deleted redex. -/
theorem disjoint_site_inside (C : SyntaxContext) {H : ParallelHistory T U}
    (ordinary : Atomic H) (positive : 0<H.length)
    (scopedHistory : Internal C.path H) (region : Internal site H)
    (apart : DisjointPositions (C.path++p) site) : ∃ q,site=C.path++q := by
  have nonempty : H.derivation.paths≠[] := by
    intro empty
    have length := ordinary.paths_length
    rw [empty] at length
    simp only [List.length_nil] at length
    omega
  cases paths : H.derivation.paths with
  | nil => exact False.elim (nonempty paths)
  | cons z zs =>
    have member : z∈H.derivation.paths := by rw [paths]; exact List.mem_cons_self
    obtain ⟨a,za⟩ := scopedHistory z member
    obtain ⟨b,zb⟩ := region z member
    rcases List.prefix_or_prefix_of_prefix (show C.path <+: z from ⟨a,za.symm⟩)
        (show site <+: z from ⟨b,zb.symm⟩) with left | right
    · obtain ⟨q,hq⟩ := left
      exact ⟨q,hq.symm⟩
    · obtain ⟨q,hq⟩ := right
      exact False.elim (apart.2 ⟨q++p,by rw [←hq,List.append_assoc]⟩)

private theorem mapped_paths_injective (pre : Path) {xs ys : List Path}
    (equal : xs.map (fun q => pre++q)=ys.map (fun q => pre++q)) : xs=ys := by
  have dropped := congrArg (List.map (List.drop pre.length)) equal
  simpa only [List.map_map,Function.comp_def,List.drop_left,List.map_id_fun'] using dropped

theorem liftStep_injective (C : SyntaxContext) (h k : ParallelStep F t u)
    (equal : C.liftStep h=C.liftStep k) : h=k := by
  have paths := congrArg ParallelStep.paths equal
  rw [C.liftStep_paths,C.liftStep_paths] at paths
  apply h.ext_data k (mapped_paths_injective C.path paths)
  exact Marked.complete_unique
    ⟨((Marked.completeOld_iff _ _).mp h.complete).1.steps,
      ((Marked.completeOld_iff _ _).mp h.complete).2⟩
    ⟨((Marked.completeOld_iff _ _).mp k.complete).1.steps,
      ((Marked.completeOld_iff _ _).mp k.complete).2⟩

private theorem replace_first {h : ParallelStep F t u} {k : ParallelStep G t u}
    (eq : F=G) (he : HEq h k) (row : StepProjection h σ τ last) : StepProjection k σ τ last := by
  cases eq
  cases eq_of_heq he
  exact row

private theorem replace_last {h : ParallelStep F v w} {k : ParallelStep G v w}
    (eq : F=G) (he : HEq h k) (row : StepProjection first σ τ h) : StepProjection first σ τ k := by
  cases eq
  cases eq_of_heq he
  exact row

private theorem reindex_heq (h : ParallelStep F t u) (eq : F=G)
    (members : ∀ p,p∈F ↔ p∈G) : HEq h (h.reindex G members) := by
  cases eq
  rfl

/-- Reflect a row at a specified deleted beta contraction. The source's
geometric rules guarantee the final singleton; no local row is assumed. -/
theorem reflectBetaRow (C : SyntaxContext) (R : BetaAt t p u)
    {σ : ParallelHistory (C.plug t) V} {τ : ParallelHistory (C.plug u) W}
    (last : ParallelStep [C.path++p] V W)
    (row : StepProjection (singleContraction (C.liftBeta R)) σ τ last)
    (ha : Atomic σ) (hb : Atomic τ) (hi : Internal C.path σ) (hj : Internal C.path τ) :
    ∃ v w, ∃ top : ParallelHistory t v, ∃ bottom : ParallelHistory u w,
      ∃ final : ParallelStep [p] v w, Atomic top ∧ Atomic bottom ∧
      StepProjection (singleContraction R) top bottom final ∧
      V=C.plug v ∧ W=C.plug w ∧ HEq σ (C.liftHistory top) ∧ HEq τ (C.liftHistory bottom) := by
  have names : [C.path++p]=C.selection [p] := by rw [C.selection_eq_map]; rfl
  have firstRow := replace_first names (C.liftStep_single_heq R).symm row
  let globalLast := last.reindex (C.selection [p]) (fun q => by rw [names])
  have lastEq := reindex_heq last names (fun q => by rw [names])
  have globalRow := replace_last names lastEq firstRow
  change StepProjection (C.liftStep (singleContraction R)) σ τ globalLast at globalRow
  obtain ⟨a,v,w,h,top,bottom,final,hat,hbt,localRow,endpoint,veq,weq,heq,topEq,bottomEq,_⟩ :=
    C.reflectScopedProjection globalRow ha hb hi hj
  have same : u=a := C.plug_injective endpoint
  cases same
  have firstEqual : singleContraction R=h := C.liftStep_injective _ _ (eq_of_heq heq)
  rw [←firstEqual] at localRow
  exact ⟨v,w,top,bottom,final,hat,hbt,localRow,veq,weq,topEq,bottomEq⟩

private theorem reflect_region_root (C : SyntaxContext) (R : BetaAt t p u)
    (σ : ParallelHistory (C.plug t) V) (ha : Atomic σ)
    (τ : ParallelHistory (C.plug u) W) (hb : Atomic τ) (last : ParallelStep G V W)
    (row : StepProjection (singleContraction (C.liftBeta R)) σ τ last)
    (positive : 0<σ.length) (insideTail : Internal C.path τ)
    (region : Path) (inside : Internal region σ)
    (geometry : DisjointPositions (C.path++p) region ∨ region=(C.path++p)++[.fn]) :
    ∃ a : ExtractionRun u, ∃ b : ExtractionRun t,
      ExtractionRun.of τ hb=C.liftRun a ∧ ExtractionRun.of σ ha=C.liftRun b ∧ RootExtraction R a b := by
  have topInside : Internal C.path σ := row.internal_reflect ha hb ⟨t,C.lookup t⟩
    (by intro q hq; cases List.mem_singleton.mp hq; exact ⟨p,rfl⟩) insideTail
  have outside : ¬∃ q,C.path++p=region++q := by
    rcases geometry with apart | function
    · exact apart.2
    · rintro ⟨q,hq⟩
      rw [function] at hq
      have lengths := congrArg List.length hq
      simp only [List.length_append,List.length_singleton] at lengths
      omega
  have finalSelection := row.final_selection_singleton rfl
    ⟨C.path++p,(C.liftBeta R).redex⟩ rfl ha inside outside
  cases finalSelection
  obtain ⟨v,w,top,bottom,final,hat,hbt,localRow,veq,weq,topEq,bottomEq⟩ :=
    C.reflectBetaRow R last row ha hb topInside insideTail
  cases veq
  cases weq
  have sameTop : σ=C.liftHistory top := eq_of_heq topEq
  have sameBottom : τ=C.liftHistory bottom := eq_of_heq bottomEq
  have localPositive : 0<top.length := by
    rw [sameTop,C.liftHistory_length] at positive
    exact positive
  have sourceEq : ExtractionRun.of τ hb=C.liftRun (.of bottom hbt) := by
    apply ExtractionRun.ext_paths
    exact congrArg (fun h => h.derivation.paths) sameBottom
  have targetEq : ExtractionRun.of σ ha=C.liftRun (.of top hat) := by
    apply ExtractionRun.ext_paths
    exact congrArg (fun h => h.derivation.paths) sameTop
  refine ⟨.of bottom hbt,.of top hat,sourceEq,targetEq,?_⟩
  rcases geometry with apart | function
  · obtain ⟨site,siteEq⟩ := C.disjoint_site_inside ha
      (by rw [sameTop,C.liftHistory_length]; exact localPositive) topInside inside apart
    have localApart : DisjointPositions p site := C.disjoint_reflect (siteEq ▸ apart)
    have localInside : Internal site top := by
      rw [siteEq,sameTop] at inside
      exact (C.internal_lift_iff top).mp inside
    exact .disjoint top hat bottom hbt final localRow localPositive site localApart localInside
  · have localInside : Internal (p++[.fn]) top := by
      rw [function,sameTop] at inside
      have normalized : Internal (C.path++(p++[.fn])) (C.liftHistory top) := by
        simpa only [List.append_assoc] using inside
      exact (C.internal_lift_iff top).mp normalized
    exact .functionPart top hat bottom hbt final localRow localPositive localInside

/-- Reflect all four genuine root extraction rules from an arbitrary
context-confined ordinary tail. Both local runs are actually constructed. -/
theorem reflectRootExtraction (C : SyntaxContext) (R : BetaAt t p u)
    {r : ExtractionRun (C.plug u)} {s : ExtractionRun (C.plug t)}
    (root : RootExtraction (C.liftBeta R) r s) (inside : Internal C.path r.history) :
    ∃ a : ExtractionRun u, ∃ b : ExtractionRun t,
      r=C.liftRun a ∧ s=C.liftRun b ∧ RootExtraction R a b := by
  cases root with
  | residual S A old =>
    obtain ⟨q,pathS⟩ := (Internal.single_iff S).mp inside
    cases pathS
    obtain ⟨v,localS,endpointS⟩ := C.reflectBeta S
    cases endpointS
    have firstInside : Internal C.path (.single (singleContraction (C.liftBeta R))) :=
      (Internal.single_iff _).mpr ⟨p,rfl⟩
    obtain ⟨a,pathA⟩ := (ParallelHistory.single (singleContraction (C.liftBeta R))).residual_reflect_internal
      firstInside ⟨_,A.redex⟩ ⟨_,S.redex⟩ ⟨q,rfl⟩ old
    cases pathA
    obtain ⟨w,localA,endpointA⟩ := C.reflectBeta A
    cases endpointA
    have localOld : (singleContraction R).derivation.Residual ⟨a,localA.redex⟩ ⟨q,localS.redex⟩ :=
      ((singleContraction R).derivation.prefix_residual_iff
        (singleContraction (C.liftBeta R)).derivation (C.lookup t) (by rfl)
        ⟨a,localA.redex⟩ ⟨q,localS.redex⟩ ⟨_,A.redex⟩ ⟨_,S.redex⟩ rfl rfl).mp old
    refine ⟨.of (.single (singleContraction localS)) (.single localS),
      .of (.single (singleContraction localA)) (.single localA),?_,?_,
      .residual localS localA localOld⟩
    · apply ExtractionRun.ext_paths; rw [C.liftRun_paths]; rfl
    · apply ExtractionRun.ext_paths; rw [C.liftRun_paths]; rfl
  | disjoint σ ha τ hb last row positive site apart region =>
    exact reflect_region_root C R σ ha τ hb last row positive inside site region (.inl apart)
  | functionPart σ ha τ hb last row positive region =>
    exact reflect_region_root C R σ ha τ hb last row positive inside _ region (.inr rfl)
  | argumentPart σ ha τ hb positive lift =>
    have originalInside : Internal C.path τ := by
      intro q hq
      rw [lift.original_paths] at hq
      obtain ⟨z,_,rfl⟩ := List.mem_map.mp hq
      exact ⟨(p++[.arg])++z,by simp only [List.append_assoc]⟩
    obtain ⟨v,copy,copyAtomic,copyEndpoint,copyEq,_⟩ := C.reflectHistory σ ha inside
    cases copyEndpoint
    obtain ⟨w,original,originalAtomic,originalEndpoint,originalEq,_⟩ := C.reflectHistory τ hb originalInside
    cases originalEndpoint
    have sameCopy : σ=C.liftHistory copy := eq_of_heq copyEq
    have sameOriginal : τ=C.liftHistory original := eq_of_heq originalEq
    let localLift : ArgumentLift R copy original := {
      body := lift.body
      argument := lift.argument
      redex := by
        have shape := lift.redex
        rw [subtermAt_append,C.lookup,Option.bind_some] at shape
        exact shape
      occurrence := lift.occurrence
      isVariable := lift.isVariable
      localPaths := lift.localPaths
      copy_paths := by
        apply mapped_paths_injective C.path
        rw [←C.liftHistory_paths copy,←sameCopy,lift.copy_paths]
        simp only [List.map_map,Function.comp_def,List.append_assoc]
      original_paths := by
        apply mapped_paths_injective C.path
        rw [←C.liftHistory_paths original,←sameOriginal,lift.original_paths]
        simp only [List.map_map,Function.comp_def,List.append_assoc]
      parallelization := StepProjection.exists_projection (singleContraction R) original }
    have localPositive : 0<copy.length := by
      rw [sameCopy,C.liftHistory_length] at positive
      exact positive
    refine ⟨.of copy copyAtomic,.of original originalAtomic,?_,?_,
      .argumentPart copy copyAtomic original originalAtomic localPositive localLift⟩
    · apply ExtractionRun.ext_paths
      exact congrArg (fun h => h.derivation.paths) sameCopy
    · apply ExtractionRun.ext_paths
      exact congrArg (fun h => h.derivation.paths) sameOriginal

/-- Reflect an arbitrary original extraction generator, including its actual
ordinary prefix, from a context lift. -/
theorem reflectExtractionStep (C : SyntaxContext) {r : ExtractionRun m}
    {s : ExtractionRun (C.plug m)} (step : ExtractionStep (C.liftRun r) s) :
    ∃ q, ExtractionStep r q ∧ s=C.liftRun q := by
  obtain ⟨t,u,p,pre,preAtomic,R,tail,result,root,sourceEq,targetEq⟩ := step.root_factor
  have sourceInside := C.liftRun_internal r
  rw [sourceEq] at sourceInside
  change Internal C.path (pre.append (.cons (singleContraction R) tail.history)) at sourceInside
  obtain ⟨preInside,restInside⟩ := (Internal.append_iff _ _).mp sourceInside
  change Internal C.path ((ParallelHistory.single (singleContraction R)).append tail.history) at restInside
  obtain ⟨headInside,tailInside⟩ := (Internal.append_iff _ _).mp restInside
  obtain ⟨a,localPre,localAtomic,endpoint,preEq,prePaths⟩ := C.reflectHistory pre preAtomic preInside
  cases endpoint
  obtain ⟨localPath,pathEq⟩ := (Internal.single_iff R).mp headInside
  cases pathEq
  obtain ⟨b,localR,endpointR⟩ := C.reflectBeta R
  cases endpointR
  have rootEq : R=C.liftBeta localR := Subsingleton.elim _ _
  rw [rootEq] at root
  obtain ⟨localTail,localResult,tailEq,resultEq,localRoot⟩ :=
    C.reflectRootExtraction localR root tailInside
  have tailPaths : tail.history.derivation.paths=
      localTail.history.derivation.paths.map (fun q => C.path++q) := by
    rw [tailEq,C.liftRun_paths]
  have resultPaths : result.history.derivation.paths=
      localResult.history.derivation.paths.map (fun q => C.path++q) := by
    rw [resultEq,C.liftRun_paths]
  let localSource : ExtractionRun m :=
    (ExtractionRun.of (.cons (singleContraction localR) localTail.history) (.cons localR localTail.atomic)).prepend
      localPre localAtomic
  let localTarget : ExtractionRun m := localResult.prepend localPre localAtomic
  have mappedSource : C.liftRun r=C.liftRun localSource := by
    apply ExtractionRun.ext_paths
    rw [sourceEq,C.liftRun_paths]
    simp only [localSource,ExtractionRun.prepend,ExtractionRun.of,
      ParallelHistory.derivation_append,Derivation.append]
    change pre.derivation.paths++((C.path++localPath)::tail.history.derivation.paths)=
      (localPre.derivation.paths++(localPath::localTail.history.derivation.paths)).map (fun q => C.path++q)
    rw [prePaths,tailPaths,List.map_append,List.map_cons]
  have localSourceEq : r=localSource := C.liftRun_injective mappedSource
  have mappedTarget : s=C.liftRun localTarget := by
    apply ExtractionRun.ext_paths
    rw [targetEq,C.liftRun_paths]
    simp only [localTarget,ExtractionRun.prepend,ExtractionRun.of,
      ParallelHistory.derivation_append,Derivation.append]
    rw [prePaths,resultPaths,List.map_append]
  have actualStep : ExtractionStep localSource localTarget := localRoot.prepend localPre localAtomic
  rw [←localSourceEq] at actualStep
  exact ⟨localTarget,actualStep,mappedTarget⟩

theorem reflectExtraction (C : SyntaxContext) {r : ExtractionRun m}
    {s : ExtractionRun (C.plug m)} (steps : Extraction (C.liftRun r) s) :
    ∃ q, Extraction r q ∧ s=C.liftRun q := by
  have main : ∀ {a b : ExtractionRun (C.plug m)}, Extraction a b →
      ∀ r : ExtractionRun m, a=C.liftRun r → ∃ q, Extraction r q ∧ b=C.liftRun q := by
    intro a b h
    induction h with
    | refl a => intro r eq; exact ⟨r,.refl _,eq⟩
    | cons head rest ih =>
      intro r eq
      rw [eq] at head
      obtain ⟨q,hq,qeq⟩ := C.reflectExtractionStep head
      obtain ⟨z,hz,zeq⟩ := ih q qeq
      exact ⟨z,.cons hq hz,zeq⟩
  exact main steps r rfl

end SyntaxContext
end Lamping.Lambda
