import Lamping.Lamping.MatchingRedexBodyLoop
import Lamping.Lamping.MatchingSharedSyntaxEvaluation
import Lamping.Lamping.SupportedExpandedLoops
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

/-- The zero-event binder invariant for ANY original lambda occurrence.
The literal ambient and loop come from actual source Matches, and the same
shared selector evaluates both paths exactly. No support or generatedness
certificate is supplied by the caller. -/
theorem Matches.original_supported_loop
    (matching : Matches g root original.erase) (initial : INIT original)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g)
    {p q : Path} {stamp : Labelled.Label} {body : LTerm}
    (atLambda : original.subterm p=some (.lam stamp body))
    (atVariable : subtermAt body.erase q=some (.var (binderDepth q))) :
    ∃ (parent leaf : RootAccess g root) (loop : List (Endpoint g)) (a b c : Context)
      (binding : BindingLoop g loop b c) (ctx : Port (g.label binding.binder).sort),
      accessWord g parent.val=p ∧accessWord g leaf.val=p++(.body::q) ∧
      leaf.val=parent.val++loop ∧accessWord g loop=q ∧
      Labelling g parent.val a b ∧
      HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      parent.val.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)) ∧
      original.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some parent.val ∧
      original.sourceTrail selection.atomWord beta.principal beta.reverseRoute (p++(.body::q))=some leaf.val ∧
      SupportedExpandedBindingLoop g root parent.val binding.binder loop ∧
      GeneratedExpandedProperPath g root parent.val ∧GeneratedExpandedProperPath g root leaf.val := by
  have lambdaLookup : subtermAt original.erase p=some (.lam body.erase) := by
    rw [←LTerm.erase_subterm,atLambda]
    rfl
  have leafLookup : subtermAt original.erase (p++(.body::q))=some (.var (binderDepth q)) := by
    rw [subtermAt_append,lambdaLookup]
    exact atVariable
  let lambdaPosition : Position original.erase := ⟨p,by rw [lambdaLookup]; rfl⟩
  let leafPosition : Position original.erase := ⟨p++(.body::q),by rw [leafLookup]; rfl⟩
  obtain ⟨parent,parentWord,_⟩ := Matches.observation g matching lambdaPosition
  obtain ⟨leaf,leafWord,_⟩ := Matches.observation g matching leafPosition
  have variableAtWord : subtermAt original.erase (accessWord g leaf.val)=some (.var (binderDepth q)) := by
    rw [leafWord]
    exact leafLookup
  obtain ⟨actualParent,loop,a,b,c,binding,ctx,_body,split,role,finish,labels,_lookup,words,depth⟩ :=
    matching.variable_binding_access leaf variableAtWord
  have occurrence := binding_prefix_depth_unique (words.symm.trans leafWord) depth.symm
  have sameParent : actualParent=parent := matching.accessWord_injective (occurrence.1.trans parentWord.symm)
  rw [sameParent] at split labels finish
  have parentEval := selection.original_access_evaluation (beta:=beta) initial matching atLambda parent parentWord
  have labelledLeaf : ∃ leafSub,original.subterm (p++(.body::q))=some leafSub := by
    rw [←LTerm.erase_subterm] at leafLookup
    cases found : original.subterm (p++(.body::q)) with
    | none => rw [found] at leafLookup; cases leafLookup
    | some sub => exact ⟨sub,rfl⟩
  obtain ⟨leafSub,leafSubLookup⟩ := labelledLeaf
  have leafEval := selection.original_access_evaluation (beta:=beta) initial matching leafSubLookup leaf leafWord
  exact ⟨parent,leaf,loop,a,b,c,binding,ctx,parentWord,leafWord,split,occurrence.2,labels,role,finish,
    parentEval,leafEval,.base parent.val loop b c binding,
    .base parent.property.1 parent.property.2.1,.base leaf.property.1 leaf.property.2.1⟩
end
end Lamping.AG
