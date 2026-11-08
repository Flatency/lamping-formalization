import Lamping.Lamping.HistoryGeneratedInvariants
import Lamping.Lamping.RootPathInputs
import Lamping.Lamping.BetaDetourBlocks
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

/-- The typed path induction proposition. Each actual syntax lookup has a
literal evaluator word which admits a finite paired assignment for every
root input. It asserts neither source-path generation nor target Matches. -/
def TypedSyntaxPaths (selection : SourceEdgeSelection original g root)
    (beta : BetaEdge g) (current : LTerm) : Prop :=
  ∀ {p sub},current.subterm p=some sub →∃ word,
    current.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some word ∧
    ∀ requested : Context,∃ output count,BetaDetourBlocks g word requested output count

/-- Reuse an independently identified evaluator word; Option equality locks
the literal path, rather than merely its terminal endpoint. -/
theorem TypedSyntaxPaths.at_word
    {selection : SourceEdgeSelection original g root} {beta : BetaEdge g} {current : LTerm}
    (typed : TypedSyntaxPaths selection beta current) {p sub word}
    (lookup : current.subterm p=some sub)
    (evaluation : current.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some word)
    (requested : Context) : ∃ output count,BetaDetourBlocks g word requested output count := by
  obtain ⟨actual,equal,assigned⟩ := typed lookup
  have same : actual=word := Option.some.inj (equal.symm.trans evaluation)
  subst actual
  exact assigned requested

/-- Zero actual events: source Matches supplies the ordinary access and
RootInputs supplies each requested assignment of that same physical path. -/
theorem Matches.typed_syntax_paths
    (matching : Matches g root original.erase) (initial : INIT original)
    (inputs : RootInputs g root)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g) :
    TypedSyntaxPaths selection beta original := by
  intro p sub lookup
  have bareLookup : subtermAt original.erase p=some sub.erase := by
    rw [←LTerm.erase_subterm,lookup]
    rfl
  let position : Position original.erase := ⟨p,by rw [bareLookup]; rfl⟩
  obtain ⟨access,word,_⟩ := Matches.observation g matching position
  refine ⟨access.val,selection.original_access_evaluation (beta:=beta) initial matching lookup access word,?_⟩
  intro requested
  obtain ⟨output,labels⟩ := inputs.access access requested
  exact ⟨output,0,labels.detour_blocks _⟩
end
end Lamping.AG
