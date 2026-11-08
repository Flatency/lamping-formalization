import Lamping.Lambda.DisjointBlocks
namespace Lamping.Lambda

/-- Literal source-history phases at a protected redex: its function,
argument, and the finite forest of disjoint right siblings. -/
def ProtectedBlocks (cut : Path) (ρ : ParallelHistory t u) : Prop :=
  ∃ v w, ∃ function : ParallelHistory t v, ∃ argument : ParallelHistory v w,
    ∃ outside : ParallelHistory w u,
      Atomic function ∧ Atomic argument ∧
      ρ=function.append (argument.append outside) ∧
      Internal (cut++[.fn]) function ∧ Internal (cut++[.arg]) argument ∧
      DisjointBlocks cut outside

theorem ProtectedBlocks.append_disjoint (blocks : ProtectedBlocks cut ρ)
    (forest : DisjointBlocks cut σ) : ProtectedBlocks cut (ρ.append σ) := by
  obtain ⟨v,w,function,argument,outside,hf,ha,whole,fi,ai,di⟩ := blocks
  refine ⟨v,w,function,argument,outside.append σ,hf,ha,?_,fi,ai,di.append forest⟩
  rw [whole,ParallelHistory.append_assoc,ParallelHistory.append_assoc]

theorem ProtectedBlocks.mapped {ρ : ParallelHistory a b} (blocks : ProtectedBlocks cut ρ)
    {global : ParallelHistory T U} (ordinary : Atomic global)
    (paths : global.derivation.paths=ρ.derivation.paths.map (fun p => pre++p)) :
    ProtectedBlocks (pre++cut) global := by
  obtain ⟨v,w,function,argument,outside,hf,ha,whole,fi,ai,di⟩ := blocks
  rw [whole] at paths
  obtain ⟨V,first,rest,firstAtomic,restAtomic,split,_,firstPaths,restPaths⟩ :=
    ordinary.split_mapped_program hf (ha.append di.atomic) paths
  obtain ⟨W,second,last,secondAtomic,lastAtomic,splitRest,_,secondPaths,lastPaths⟩ :=
    restAtomic.split_mapped_program ha di.atomic restPaths
  refine ⟨V,W,first,second,last,firstAtomic,secondAtomic,?_,?_,?_,di.mapped lastAtomic lastPaths⟩
  · rw [split,splitRest]
  · intro p hp
    rw [firstPaths] at hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨r,eq⟩ := fi q hq
    exact ⟨r,by rw [eq]; simp only [List.append_assoc]⟩
  · intro p hp
    rw [secondPaths] at hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨r,eq⟩ := ai q hq
    exact ⟨r,by rw [eq]; simp only [List.append_assoc]⟩

/-- At a root redex the protected source block theorem follows from the
actual standard application split, with an empty disjoint forest. -/
theorem Atomic.standard_root_blocks {ρ : ParallelHistory t u} (ordinary : Atomic ρ)
    (root : BetaAt t [] v) (right : RightHistory [] ρ) (standard : Standard ρ) :
    ProtectedBlocks [] ρ := by
  obtain ⟨body,arg,lookup,_⟩ := root
  have shape : t=.app (.lam body) arg := by simpa only [subtermAt,Option.some.injEq] using lookup
  have noRoot : ∀ p∈ρ.derivation.paths,p≠[] := by
    intro p hp eq
    have before := right.paths_right p hp
    rw [eq] at before
    exact LeftOf.irrefl [] before
  obtain ⟨mid,function,argument,hf,ha,whole,fi,ai⟩ := ordinary.standard_app_blocks shape noRoot standard
  exact ⟨mid,u,function,argument,.nil u,hf,ha,by simpa using whole,fi,ai,.nil u⟩

/-- Every standard ordinary program strictly to the right of an actual
protected redex splits into its function, argument and disjoint phases. -/
theorem Atomic.standard_protected_blocks {ρ : ParallelHistory t u} (ordinary : Atomic ρ)
    (root : BetaAt t cut v) (right : RightHistory cut ρ) (standard : Standard ρ) :
    ProtectedBlocks cut ρ := by
  induction cut generalizing t u v with
  | nil => exact ordinary.standard_root_blocks root right standard
  | cons edge cut ih =>
    cases t with
    | var n => obtain ⟨_,_,lookup,_⟩ := root; cases edge <;> simp [subtermAt] at lookup
    | lam bterm =>
      cases edge with
      | fn => obtain ⟨_,_,lookup,_⟩ := root; simp [subtermAt] at lookup
      | arg => obtain ⟨_,_,lookup,_⟩ := root; simp [subtermAt] at lookup
      | body =>
        let within : Internal [Step.body] ρ := fun p hp => by
          have h := right.paths_right p hp
          cases h with | child _ h => exact ⟨_,rfl⟩
        obtain ⟨localTarget,localRoot,_⟩ := (SyntaxFrame.body).beta_reflect root
        obtain ⟨b,history,atomic,std,localRight,paths,_⟩ := ordinary.standard_internal_right_reflect
          (a:=bterm) (site:=[.body]) (cut:=cut) standard within (by simp [subtermAt]) right
        exact (ih atomic localRoot localRight std).mapped ordinary paths
    | app f a =>
      cases edge with
      | body => obtain ⟨_,_,lookup,_⟩ := root; simp [subtermAt] at lookup
      | arg =>
        have inside : Internal [.arg] ρ := by
          intro p hp
          have h := right.paths_right p hp
          cases h with | child _ h => exact ⟨_,rfl⟩
        obtain ⟨localTarget,localRoot,_⟩ := (SyntaxFrame.arg f).beta_reflect root
        obtain ⟨b,history,atomic,std,localRight,paths,_⟩ := ordinary.standard_internal_right_reflect
          (a:=a) (site:=[.arg]) (cut:=cut) standard inside (by simp [subtermAt]) right
        exact (ih atomic localRoot localRight std).mapped ordinary paths
      | fn =>
        have noRoot : ∀ p∈ρ.derivation.paths,p≠[] := by
          intro p hp eq
          have h := right.paths_right p hp
          rw [eq] at h
          cases h
        obtain ⟨mid,function,argument,hf,ha,whole,fi,ai⟩ := ordinary.standard_app_blocks rfl noRoot standard
        have functionRight : RightHistory (.fn::cut) function := hf.right_of_paths (by
          intro p hp
          apply right.paths_right p
          rw [whole,ParallelHistory.derivation_append,Derivation.append]
          exact List.mem_append_left _ hp)
        have functionStandard : Standard function := by
          rw [whole] at standard
          exact standard.prefix
        obtain ⟨localTarget,localRoot,_⟩ := (SyntaxFrame.fn a).beta_reflect root
        obtain ⟨b,history,atomic,std,localRight,paths,_⟩ := hf.standard_internal_right_reflect
          (a:=f) (site:=[.fn]) (cut:=cut) functionStandard fi (by simp [subtermAt]) functionRight
        have first := (ih atomic localRoot localRight std).mapped hf paths
        have apart : DisjointPositions (.fn::cut) [.arg] :=
          DisjointPositions.head_ne (by intro eq; cases eq)
        have forest : DisjointBlocks (.fn::cut) argument := by
          simpa using (DisjointBlocks.cons ha ai apart (DisjointBlocks.nil _))
        rw [whole]
        exact first.append_disjoint forest

end Lamping.Lambda

