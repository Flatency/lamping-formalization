import Lamping.Lamping.HistoryGeneratedInvariants
import Lamping.Lamping.BetaDetourBlocks
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {original : LTerm}

/-- The assignment component for a SPECIFIED current binder occurrence.
Both paths are the literal words of the same shared evaluator. Given a
whole OLD body stream and the SAME-input ambient labelling, this proposition
requires only their shell relation at the actual binder index. It asserts
neither existence of those assignments nor any NEW path labelling.

No support premise is needed: evaluator equalities and the lambda-context
endpoint identify this exact ambient/loop occurrence. The proposition is
proved along actual histories; declaring it is not such a proof. -/
def TypedSyntaxBinders (selection : SourceEdgeSelection original g root)
    (beta : BetaEdge g) (current : LTerm) : Prop :=
  ∀ {p stamp body},current.subterm p=some (.lam stamp body) →
  ∀ {q},subtermAt body.erase q=some (.var (binderDepth q)) →
  ∀ {ambient loop : List (Endpoint g)} {binder : N} {ctx : Port (g.label binder).sort},
    current.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some ambient →
    current.sourceTrail selection.atomWord beta.principal beta.reverseRoute (p++(.body::q))=some (ambient++loop) →
    (g.label binder).sort=.op .lam →HEq ctx (Sum.inl () : Port (.op .lam)) →
    ambient.getLast?=some (g.wire (.inl ⟨binder,ctx⟩)) →
    ∀ {input output seam : Context} {count : Nat},
      BetaDetourBlocks g (ambient++loop) input output count →
      ExpandedLabelling g ambient input seam →
      Context.SameShell (g.label binder).index seam output
end
end Lamping.AG
