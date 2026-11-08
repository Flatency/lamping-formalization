import Lamping.Lamping.InitialPathRelabelling
import Lamping.Lamping.GlobalPathInvariants
namespace Lamping.Checks.InitialAccess
open Graph AG Lambda
private abbrev g := (encode 0 (.var 0)).net
private def shortPath : List (Endpoint g) := [.inr (.inl (.inl ()))]
private def longPath : List (Endpoint g) := [.inr (.inl (.inl ())),.inl ⟨(),.inl ()⟩]
private theorem first_labels : InitialLabelling (g:=g) shortPath Context.empty Context.empty := .single _ _
private theorem next_labels : InitialLabelling (g:=g) longPath Context.empty Context.empty := by
  have step : Passage 0 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
    simpa only [Context.replace_zero,Context.cons_empty] using Passage.cro (i:=0) Context.empty Context.empty
  exact .cons (.node () _ _ step) (.single _ _)
-- The proper-terminal hypotheses cannot be removed from word determinism:
-- a zero-token control prefix can continue without changing the syntax word.
example : ¬∀ (es fs : List (Endpoint g)),
    InitialLabelling (g:=g) es Context.empty Context.empty →
    InitialLabelling (g:=g) fs Context.empty Context.empty →
    es.head?=fs.head? →accessWord g es=accessWord g fs →es=fs := by
  intro wrong
  have same := wrong shortPath longPath first_labels next_labels rfl rfl
  have length := congrArg List.length same
  change 1=2 at length
  cases length
example (input : Context) : ∃ last,Labelling g longPath input last :=
  encode_root_relabel_input (.var 0) 0 longPath rfl ⟨_,_,next_labels.labelling⟩ input
example (t : Term) (n : Nat) (es fs : RootAccess (encode n t).net (.inl ()))
    (word : accessWord (encode n t).net es.val=accessWord (encode n t).net fs.val) : es=fs :=
  encode_accessWord_injective t n word
example {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    {graph : Net signature N B W} {es : List (Endpoint graph)} {a b : Context}
    (labels : Labelling graph es a b) :
    ∃ cs,ContextTrace graph es cs ∧Labelling graph es a b ∧es.length=cs.length := by
  obtain ⟨cs,trace,first,last⟩ := labels.contextTrace
  exact ⟨cs,trace,ContextTrace.labelling graph trace first last,trace.length⟩
#print axioms InitialLabelling.access_word_unique
#print axioms encode_accessWord_injective
#print axioms encode_root_relabel_input
#print axioms Labelling.contextTrace
end Lamping.Checks.InitialAccess
