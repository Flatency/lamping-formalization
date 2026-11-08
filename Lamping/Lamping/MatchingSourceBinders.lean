import Lamping.Lamping.MatchingVariableAccess
import Lamping.Lambda.SourceBinderOccurrences
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
/-- Static original binder identity is realized by the SAME literal prefix
and physical binding loop supplied by source Matches. Lexical position/depth,
not equality of potentially repeated labels, identifies the occurrence. -/
theorem Matches.original_source_binder {original : LTerm}
    (matching : Matches g root original.erase)
    (atVariable : SourceSubterm [] .external original p env sourceCtx (.var variableLabel index))
    (bound : sourceBinder env index=.lamBind origin)
    (access : RootAccess g root) (word : accessWord g access.val=p) :
    ∃ (parent : RootAccess g root) (loop : List (Endpoint g)) (a b c : Context)
      (binding : BindingLoop g loop b c) (ctx : Port (g.label binding.binder).sort) (body : LTerm),
      access.val=parent.val++loop ∧ HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      parent.val.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)) ∧
      Labelling g parent.val a b ∧
      original.subterm (accessWord g parent.val)=some (.lam origin body) ∧
      p=accessWord g parent.val++(.body::accessWord g loop) ∧
      index=binderDepth (accessWord g loop) := by
  have originalVar : subtermAt original.erase p=some (.var index) := by
    rw [←LTerm.erase_subterm,atVariable.lookup]
    rfl
  have variableLookup : subtermAt original.erase (accessWord g access.val)=some (.var index) := by
    simpa only [word] using originalVar
  obtain ⟨parent,loop,a,b,c,binding,ctx,_,split,role,finish,labels,_,words,depth⟩ :=
    matching.variable_binding_access access variableLookup
  obtain ⟨staticParent,staticTail,oldBody,staticWord,atBinder,staticDepth⟩ :=
    atVariable.sourceBinder_occurrence bound
  have paths : accessWord g parent.val++(.body::accessWord g loop)=staticParent++(.body::staticTail) :=
    words.symm.trans (word.trans staticWord)
  have depths : binderDepth (accessWord g loop)=binderDepth staticTail := depth.symm.trans staticDepth
  have same := binding_prefix_depth_unique paths depths
  rw [←same.1] at atBinder
  exact ⟨parent,loop,a,b,c,binding,ctx,oldBody,split,role,finish,labels,atBinder,word.symm.trans words,depth⟩
end
end Lamping.AG
