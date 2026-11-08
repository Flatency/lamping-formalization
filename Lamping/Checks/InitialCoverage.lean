import Lamping.Lamping.InitialBoundAccess
import Lamping.Lamping.InitialBindingSuffix
import Lamping.Lamping.InitialMatching
import Lamping.Lamping.InitialNesting
import Lamping.Lamping.OrdinaryPrefixRelabelling
import Lamping.Lamping.InitialFullIndependence
namespace Lamping.Checks.InitialCoverage
open Graph AG Lambda
private def nestedDup : Term := .lam (.lam (.app (.var 1) (.var 1)))
private theorem nestedClosed : Closed nestedDup := by change 1<2 ∧1<2; decide
private def functionAddress : Path := [.body,.body,.fn]
private def argumentAddress : Path := [.body,.body,.arg]

-- Two distinct physical variable accesses have the same variable index in
-- the syntax. Their different addresses still distinguish the actual paths.
example (n : Nat) (input : Context) :
    ∃ left right : RootAccess (encode n nestedDup).net (.inl ()),
      left≠right ∧accessWord (encode n nestedDup).net left.val=functionAddress ∧
      accessWord (encode n nestedDup).net right.val=argumentAddress ∧
      accessKind (encode n nestedDup).net left.val=some .var ∧
      accessKind (encode n nestedDup).net right.val=some .var := by
  obtain ⟨left⟩ := encode_boundvar_access nestedDup n functionAddress 1 rfl (by decide) input
  obtain ⟨right⟩ := encode_boundvar_access nestedDup n argumentAddress 1 rfl (by decide) input
  refine ⟨left.rootAccess,right.rootAccess,?_,left.word,right.word,left.terminal,right.terminal⟩
  intro same
  have words := congrArg (fun p : RootAccess (encode n nestedDup).net (.inl ()) =>
    accessWord (encode n nestedDup).net p.val) same
  dsimp only at words
  rw [left.word,right.word] at words
  cases words

-- Check arbitrary positions of this closed sharing example, not just λI.
example (n : Nat) (p : Position nestedDup) (input : Context) :
    ∃ es : RootAccess (encode n nestedDup).net (.inl ()),
      accessWord (encode n nestedDup).net es.val=p.val :=
  encode_closed_access_coverage nestedDup nestedClosed n p input

-- Both actual nested variable accesses have binding occurrence index 1.
example (n : Nat) : ∃ es : RootAccess (encode n nestedDup).net (.inl ()),
    accessWord (encode n nestedDup).net es.val=argumentAddress ∧
    BindingSuffix (encode n nestedDup).net es.val 1 ∧
    ∀ k,BindingSuffix (encode n nestedDup).net es.val k → k=1 := by
  obtain ⟨es,word⟩ := encode_closed_access_coverage nestedDup nestedClosed n
    ⟨argumentAddress,by decide⟩ Context.empty
  have lookup : subtermAt nestedDup (accessWord (encode n nestedDup).net es.val)=some (.var 1) := by
    rw [word]; rfl
  have observed := encode_closed_var_observes nestedDup nestedClosed n es 1 lookup
  exact ⟨es,word,observed.2.1,observed.2.2⟩

example (n : Nat) : Matches (encode n nestedDup).net (.inl ()) nestedDup :=
  encode_closed_matches nestedDup nestedClosed n

example (t : Term) (closed : Closed t) (n : Nat) : Matches (encode n t).net (.inl ()) t :=
  encode_closed_matches t closed n

-- The shared closed example retains Nesting at a nonzero translation level;
-- no two visits to one physical context edge are possible, whatever labels.
example (es : List (Endpoint (encode 7 nestedDup).net))
    (proper : ProperPath (encode 7 nestedDup).net es)
    (rooted : es.head?=some (.inr (.inl (.inl ())))) (i j : Nat)
    (edge : Endpoint (encode 7 nestedDup).net) (atI : es[i]?=some edge) (atJ : es[j]?=some edge)
    (role : ProperRole) (n : Nat) (context : role=.appCtx ∨role=.lamCtx)
    (target : AtProperRole (encode 7 nestedDup).net (.inl ()) ((encode 7 nestedDup).net.wire edge) role n) : i=j :=
  encode_context_no_revisit nestedDup 7 es proper rooted i j edge atI atJ role n context target

example (n : Nat) : Transparency (encode n nestedDup).net (.inl ()) :=
  encode_closed_transparency nestedDup nestedClosed n

-- The chosen argument occurrence crosses both its actual Cro/Bra and shared
-- Fan. Its emitted word is still the argument address at arbitrary input.
example (n : Nat) (input : Context) :
    ∃ output, ∃ p : LocalPath (encode n (.app (.var 0) (.var 0))).net
        (.inl ()) (.inr ⟨0,by decide⟩) input output,
      accessTokens (encode n (.app (.var 0) (.var 0))).net p.edges=[.arg] := by
  exact InitialOffsets.FreeOccurrence.realized
    (InitialOffsets.FreeOccurrence.argument (.var 0) (.leaf 0)) n input

#print axioms InitialOffsets.FreeOccurrence.realized
#print axioms InitialOffsets.freeOccurrence_of_lookup
#print axioms encode_nonvar_access
#print axioms encode_boundvar_access
#print axioms encode_closed_access_coverage
#print axioms initial_bound_binding_access
#print axioms encode_closed_var_observes
#print axioms encode_closed_matches
#print axioms encode_closed_transparency
#print axioms encode_nesting
#print axioms encode_context_no_revisit
#print axioms Independence.rooted_source_prefix

example (t : Term) (closed : Closed t) (n : Nat) :
    OrdinaryPathInvariants (encode n t).net (.inl ()) :=
  encode_closed_ordinary_invariants t closed n

-- A nonzero initial level and nested shared variables exercise the complete
-- bundle; the binding branch is included, rather than only context targets.
example : Independence (encode 7 nestedDup).net (.inl ()) :=
  encode_closed_independence nestedDup nestedClosed 7

-- The actual shared argument control suffix has width 1, strictly above
-- its application source level 0; its Cro/Bra/Fan shape transports any tail.
private def sharedArgumentShape : InitialOffsets.Shape := .lower (.base []) [true]
example : InitialOffsets.eventsOfEdges (DupNet 0) dupRightControlEdges=
    sharedArgumentShape.events 0 := rfl
example (input tail : Context) :
    sharedArgumentShape.execute 0 (input.replace 1 tail)=
      (sharedArgumentShape.execute 0 input).replace 1 tail :=
  sharedArgumentShape.execute_replace 0 input tail

#print axioms encode_binding_program
#print axioms InitialOffsets.Shape.execute_replace
#print axioms encode_closed_independence
#print axioms encode_closed_ordinary_invariants
end Lamping.Checks.InitialCoverage
