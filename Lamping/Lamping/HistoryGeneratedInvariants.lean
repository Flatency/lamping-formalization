import Lamping.Lamping.MatchingOriginalSupportedLoops
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

/-- The generated-path component of the history induction. This is an
induction proposition, not an assumed development correctness certificate. -/
def GeneratedSyntaxPaths (selection : SourceEdgeSelection original g root)
    (beta : BetaEdge g) (current : LTerm) : Prop :=
  ∀ {p sub},current.subterm p=some sub →∃ word,
    current.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some word ∧
    GeneratedExpandedProperPath g root word

/-- The binder component of the same induction. The ambient and the binding
loop are literal evaluator words at this lambda OCCURRENCE and its bound
leaf. The finite support retains previous rooted bodies, and actual context
port metadata identifies the physical binder. This asserts no labellability. -/
def SupportedSyntaxBinders (selection : SourceEdgeSelection original g root)
    (beta : BetaEdge g) (current : LTerm) : Prop :=
  ∀ {p stamp body},current.subterm p=some (.lam stamp body) →
  ∀ {q},subtermAt body.erase q=some (.var (binderDepth q)) →
  ∃ (ambient loop : List (Endpoint g)) (binder : N) (ctx : Port (g.label binder).sort),
    current.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some ambient ∧
    current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (p++(.body::q))=some (ambient++loop) ∧
    SupportedExpandedBindingLoop g root ambient binder loop ∧
    (g.label binder).sort=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam)) ∧
    ambient.getLast?=some (g.wire (.inl ⟨binder,ctx⟩))

/-- Zero actual events: ordinary source Matches supplies every generated
path, with exactly the same selector at all positions. -/
theorem Matches.generated_syntax_paths
    (matching : Matches g root original.erase) (initial : INIT original)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g) :
    GeneratedSyntaxPaths selection beta original := by
  intro p sub lookup
  have bareLookup : subtermAt original.erase p=some sub.erase := by
    rw [←LTerm.erase_subterm,lookup]
    rfl
  let position : Position original.erase := ⟨p,by rw [bareLookup]; rfl⟩
  obtain ⟨access,word,_⟩ := Matches.observation g matching position
  exact ⟨access.val,selection.original_access_evaluation (beta:=beta) initial matching lookup access word,
    .base access.property.1 access.property.2.1⟩

/-- Zero actual events: original source binder occurrences provide all
support trees and their exact ambient/leaf words, with no caller loop. -/
theorem Matches.supported_syntax_binders
    (matching : Matches g root original.erase) (initial : INIT original)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g) :
    SupportedSyntaxBinders selection beta original := by
  intro p stamp body atLambda q atVariable
  obtain ⟨parent,leaf,loop,_a,_b,_c,binding,ctx,_parentWord,_leafWord,split,_loopWord,
      _labels,role,finish,parentEval,leafEval,support,_parentGen,_leafGen⟩ :=
    matching.original_supported_loop initial selection beta atLambda atVariable
  exact ⟨parent.val,loop,binding.binder,ctx,parentEval,by simpa only [split] using leafEval,
    support,binding.isLam,role,finish⟩
end
end Lamping.AG
