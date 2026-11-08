import Lamping.Lamping.GraphIndexedBalance
import Lamping.Lamping.HighTailTransport
namespace Lamping.AG
open Graph Lambda

/-- The tail and strict-width component of Independence holds after every
actual finite rewrite trace. Smaller-source-index arbitrary-input existence
and Nesting/Transparency are separate obligations. -/
theorem initial_trace_independence_tail (t : Term) (target : ActualNet (Boundary t))
    (schemas : List Schema) (trace : GraphTrace (ActualNet.initial t) target schemas)
    (es : List (Endpoint target.net)) (e f : Endpoint target.net)
    (sr tr : ProperRole) (m n : Nat) (a b : Context)
    (first : es.head?=some e) (finish : es.getLast?=some (target.net.wire f))
    (atSource : AtProperRole target.net (.inl ()) e sr m) (outgoing : sr.outgoing)
    (atTarget : AtProperRole target.net (.inl ()) f tr n) (incoming : tr.incoming)
    (fw : Forward target.net es) (labels : Labelling target.net es a b) :
    ∃ width,m≤width ∧ (sr=.appArg → m<width) ∧
      (∀ c,b=b.replace (tr.terminalWidth n) c → a=a.replace width c) ∧
      ∀ c,Labelling target.net es (a.replace width c) (b.replace (tr.terminalWidth n) c) := by
  obtain ⟨balance⟩ := initial_trace_indexed_balance t target schemas trace
  exact balance.independence_tail (.inl ()) rfl es e f sr tr m n a b first finish
    atSource outgoing atTarget incoming fw labels
end Lamping.AG
