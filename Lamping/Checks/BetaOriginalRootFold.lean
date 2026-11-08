import Lamping.Lamping.BetaOriginalRootFold
import Lamping.Checks.FunctionWrappedReachable
import Lamping.Checks.WrappedSuccessfulChains

namespace Lamping.Checks.BetaOriginalRootFold
open AG Graph Lambda Lambda.Labelled
private noncomputable abbrev site := FunctionWrappedReachable.concrete.site
private abbrev original := WrappedSuccessfulChains.original
private abbrev current := WrappedSuccessfulChains.current

theorem actual_closed_beta_all_root_fold :
    INIT original ∧Closed original.erase ∧
    GraphStep (.beta 0) (ActualNet.initial FunctionWrappedReachable.term)
      (ActualNet.ofNet site.reduce) ∧
    ∃ (weights : Endpoint site.reduce→EdgeWord)
      (rootAccess functionAccess : RootAccess site.reduce (.inl ())),
      OriginalWordReversal weights ∧OriginalRootFold site.reduce (.inl ()) current weights ∧
      accessWord site.reduce rootAccess.val=[] ∧
      accessWord site.reduce functionAccess.val=[.fn] ∧
      current.originalIncomingTrail []=some (physicalOriginalWord weights rootAccess.val) ∧
      current.originalIncomingTrail [.fn]=some (physicalOriginalWord weights functionAccess.val) ∧
      (∃body,current.subterm [.fn]=some (.lam WrappedSuccessfulChains.functionLabel body)) ∧
      (∀n,WrappedSuccessfulChains.functionLabel≠Label.atom n) := by
  refine ⟨WrappedSuccessfulChains.initial,WrappedSuccessfulChains.sourceClosed,
    FunctionWrappedReachable.actual_beta_step,?_⟩
  obtain ⟨addr⟩ := encode_addressing original.erase 0
  let initialWeights := initialOriginalWeights original 0 addr
  have initialFold := initial_original_root_fold original WrappedSuccessfulChains.sourceClosed 0 addr
  have initialReversal : OriginalWordReversal initialWeights :=
    symmetrizedOriginalWord_reversal (encode 0 original.erase).net (initialOriginalEntry original 0 addr)
  let oldWeights : Endpoint site.net→EdgeWord :=
    fun e=>initialWeights (FunctionWrappedReachable.concrete.sourceIso.symm.ends e)
  have oldFold : OriginalRootFold site.net (.inl ()) original oldWeights :=
    FunctionWrappedReachable.concrete.sourceIso.original_root_fold initialWeights initialFold
  have oldReversal : OriginalWordReversal oldWeights :=
    FunctionWrappedReachable.concrete.sourceIso.original_word_reversal initialWeights initialReversal
  obtain ⟨flow⟩ := encode_flowBalance FunctionWrappedReachable.term 0
  obtain ⟨balance⟩ := encode_indexed_balance FunctionWrappedReachable.term 0
  have matching : Matches site.net (.inl ()) original.erase :=
    FunctionWrappedReachable.concrete.sourceIso.matches
      (encode_closed_matches FunctionWrappedReachable.term FunctionWrappedReachable.closed 0)
  obtain ⟨_localTarget,_localHistory,_sameErase,edge,_selection,_geometry,reversal,fold⟩ :=
    site.beta_original_word_root_access WrappedSuccessfulChains.initial (.nil original)
      WrappedSuccessfulChains.sourceClosed matching
      (FunctionWrappedReachable.concrete.sourceIso.rootInputs
        (encode_closed_independence FunctionWrappedReachable.term FunctionWrappedReachable.closed 0).rootInputs)
      (FunctionWrappedReachable.concrete.sourceIso.flowBalance flow) rfl
      (FunctionWrappedReachable.concrete.sourceIso.indexed_balance balance) rfl
      (FunctionWrappedReachable.concrete.sourceIso.transparency
        (encode_closed_transparency FunctionWrappedReachable.term FunctionWrappedReachable.closed 0))
      FunctionWrappedReachable.relative
      (by simp [FunctionWrappedReachable.endpoint,Marked.Normal])
      WrappedSuccessfulChains.actualHistory oldWeights oldReversal oldFold
  let weights := site.betaOriginalWordWeights edge oldWeights
  let rootPosition : Position current.erase := ⟨[],rfl⟩
  let functionPosition : Position current.erase := ⟨[.fn],rfl⟩
  obtain ⟨rootAccess,rootWord,_⟩ := Matches.observation _ FunctionWrappedReachable.beta_matches rootPosition
  obtain ⟨functionAccess,functionWord,_⟩ := Matches.observation _ FunctionWrappedReachable.beta_matches functionPosition
  have rootFold := fold rootAccess
  have functionFold := fold functionAccess
  rw [rootWord] at rootFold
  rw [functionWord] at functionFold
  refine ⟨weights,rootAccess,functionAccess,reversal,fold,rootWord,functionWord,
    rootFold,functionFold,WrappedSuccessfulChains.function_lambda_lookup,?_⟩
  intro n impossible
  cases impossible

#print axioms actual_closed_beta_all_root_fold
end Lamping.Checks.BetaOriginalRootFold
