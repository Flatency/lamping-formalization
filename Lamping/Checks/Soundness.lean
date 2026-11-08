import Lamping.Lamping.ReachableNormalForms
import Lamping.Lamping.BetaCompleteMatching
import Lamping.Lamping.BetaSyntaxTrailContraction
import Lamping.Lamping.BetaSourceRouteWords
import Lamping.Lamping.BetaAtomicContraction
import Lamping.Lamping.RelativeHistoryTyped
import Lamping.Lamping.HistoryTypedPathStep
import Lamping.Lamping.MatchingSpecifiedBindingShell
import Lamping.Lamping.HistoryTypedCopiedStep
import Lamping.Lamping.RelativeHistoryGenerated
import Lamping.Lamping.HistoryGeneratedCopyStep
import Lamping.Lamping.MatchingCopiedSupportedLoops
import Lamping.Lamping.MatchingOriginalSupportedLoops
import Lamping.Lamping.MatchingFirstHistoryEvaluation
import Lamping.Lamping.MatchingSelectedPrincipalWord
import Lamping.Lamping.MatchingNestedCoherence
import Lamping.Lamping.MatchingNestedHistoryGenerated
import Lamping.Lamping.MatchingFirstContractumCoherence
import Lamping.Lamping.MatchingNestedGeneratedBase
import Lamping.Lamping.MatchingFirstInsertionCoherence
import Lamping.Lamping.MatchingFirstBetaPositions
import Lamping.Lamping.GeneratedNestedInsert
import Lamping.Lamping.MatchingBetaGeneratedBase
import Lamping.Lamping.SourceActionAccess
import Lamping.Lamping.SourceActionLocalExpansion
import Lamping.Lamping.SourceActionPassiveBranch
import Lamping.Lamping.RootActionTypedInputs
import Lamping.Lamping.RootBetaInputs
import Lamping.Lamping.ReachableTransparency
import Lamping.Lamping.IndexedPairedTransparency
import Lamping.Lamping.GraphIndexedBalance
import Lamping.Lamping.IndexedBetaCoherence
import Lamping.Lamping.IndexedLambdaShellReflection
import Lamping.Lamping.RootBinderUniform
import Lamping.Lamping.RootPathInputs
import Lamping.Lamping.BetaForwardInputs
import Lamping.Lamping.BetaUnpairedPrefix
import Lamping.Lamping.BetaProperAncestors
import Lamping.Lamping.BetaTransparency
import Lamping.Lamping.ActionKeptTransparency
import Lamping.Lamping.ActionTransparency
import Lamping.Lamping.StepTransparency
import Lamping.Lamping.PathShellReflection
import Lamping.Lamping.BetaBindingLoopContraction
import Lamping.Lamping.ActionTypedInputs
import Lamping.Lamping.MatchingUniqueness
import Lamping.Lamping.MatchingInitial
import Lamping.Lamping.PathLabelDeterminism
import Lamping.Lamping.ExpandedMarkerPaths
import Lamping.Lamping.ExpandedOrdinaryIndependence
import Lamping.Lamping.ExpandedBinderOccurrences
import Lamping.Lamping.InitialExpandedInsertion
import Lamping.Lamping.CoherentExpandedPaths
import Lamping.Lamping.FlowRootPaths
import Lamping.Lamping.PathSiteBetaDirection
import Lamping.Lamping.BetaDetourReflection
import Lamping.Lamping.PathSiteBetaCoherent
import Lamping.Lamping.BetaEncodingIso
import Lamping.Lamping.NetIsoInvariantTransport
import Lamping.Lamping.MarkerExpressions
import Lamping.Lamping.MarkerExpressionPaths
import Lamping.Lamping.MarkerBinderUniform
import Lamping.Lamping.TypedDetourRelabelling
import Lamping.Lamping.BetaResidualContraction
import Lamping.Lamping.HighTailTransport
import Lamping.Lamping.MatchingChildAccess
import Lamping.Lamping.MatchedControlInputs
import Lamping.Lamping.InitialFullIndependence
import Lamping.Checks.Paths
import Lamping.Lamping.ExpandedPrefixClosure
import Lamping.Lamping.InitialPathControls
namespace Lamping.Checks.Soundness
open AG Graph Lambda

abbrev identityNet := (encode 0 (.lam (.var 0))).net
abbrev identityRoot : Endpoint identityNet := .inr (.inl (.inl ()))
def identityVariableEdges : List (Endpoint identityNet) :=
  [identityRoot,
   .inl ⟨.inl (),lamBody⟩,
   .inr (.inr (.inr (.inl ()),true)),
   .inl ⟨.inr (),.inl ()⟩,
   .inr (.inr (.inr (.inr ⟨0,rfl⟩),false))]

example : accessWord identityNet [identityRoot] = [] := rfl
example : accessKind identityNet [identityRoot] = some .lam := rfl
example : accessWord identityNet identityVariableEdges = [.body] := rfl
example : accessKind identityNet identityVariableEdges = some .var := rfl

/-- The real encoded variable is bound by the root lambda occurrence. -/
theorem identity_binding : BindingSuffix identityNet identityVariableEdges 0 := by
  let loop := identityBindingLoop 0 Context.empty Context.empty
  refine ⟨[identityRoot],_,_,_,_,loop,.inl (),rfl,HEq.rfl,rfl,.single _ _,rfl⟩

example : ProperPath identityNet identityVariableEdges := identity_binding.labelling identityNet


/-- Exhaustive physical access classification on the literal encoding of I. -/
theorem identity_access_cases (es : RootAccess identityNet (.inl ())) :
    es.val=[identityRoot] ∨ es.val=identityVariableEdges := by
  obtain ⟨edges,hpath⟩ := es
  obtain ⟨⟨proper,fw⟩,rooted,terminal⟩ := hpath
  obtain ⟨rest,he⟩ := List.head?_eq_some_iff.mp rooted
  subst edges
  cases fw with
  | single => exact Or.inl rfl
  | node n p q ha hl hd hs =>
    cases ha
    have hq := hd.2
    cases hq
    cases hl
    cases hs with
    | single =>
      obtain ⟨k,hk⟩ := terminal
      change (none : Option AccessKind)=some k at hk
      cases hk
    | node n p q ha hl hd hs => cases ha
    | transparent w d ha hl hs =>
      cases ha; cases hl
      cases hs with
      | single =>
        obtain ⟨k,hk⟩ := terminal
        change (none : Option AccessKind)=some k at hk
        cases hk
      | node n p q ha hl hd hs =>
        cases ha
        cases q with
        | inl u =>
          cases u; cases hl
          cases hs with
          | single =>
            obtain ⟨k,hk⟩ := terminal
            change (none : Option AccessKind)=some k at hk
            cases hk
          | node n p q ha hl hd hs => cases ha
          | transparent w d ha hl hs =>
            cases ha; cases hl
            cases hs with
            | single => exact Or.inr rfl
            | node n p q ha hl hd hs =>
              cases ha
              cases hd.1
            | transparent w d ha hl hs => cases ha
        | inr u =>
          cases u
          cases hl
          obtain ⟨a,b,lab⟩ := proper
          cases lab with
          | cons h1 l2 =>
            cases l2 with
            | cons h2 l3 =>
              cases l3 with
              | cons h3 l4 =>
                cases h3 with
                | node n p q rule => exact False.elim (rule.distinct rfl)
      | transparent w d ha hl hs => cases ha
  | transparent w d ha hl hs => cases ha

theorem identity_binding_index (j : Nat) (h : BindingSuffix identityNet identityVariableEdges j) : j=0 := by
  obtain ⟨pre,edges,a,b,c,binding,ctx,he,hctx,hpre,hlabels,hj⟩ := h
  rcases binding with ⟨n,isLam,body,bind,hbody,hbind,start,finish,proper,fw,shell⟩
  cases n with
  | inr u => cases isLam
  | inl u =>
    cases u
    have hb : body=lamBody := eq_of_heq hbody
    subst body
    obtain ⟨tail,ht⟩ := List.head?_eq_some_iff.mp start
    rw [ht] at he
    cases pre with
    | nil => cases he
    | cons e pre =>
      cases pre with
      | nil =>
        have ht' : tail=[.inr (.inr (.inr (.inl ()),true)),
            .inl ⟨.inr (),.inl ()⟩,.inr (.inr (.inr (.inr ⟨0,rfl⟩),false))] := by
          exact (List.cons.inj (List.cons.inj he).2).2.symm
        rw [ht,ht'] at hj
        exact hj
      | cons e pre =>
        cases pre with
        | nil => cases he
        | cons e pre =>
          cases pre with
          | nil => cases he
          | cons e pre =>
            cases pre with
            | nil => cases he
            | cons e pre =>
              cases pre with
              | nil => cases he
              | cons e pre => cases he

def identityRootAccess : RootAccess identityNet (.inl ()) :=
  ⟨[identityRoot],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,
    rfl,⟨.lam,rfl⟩⟩⟩

def identityVariableAccess : RootAccess identityNet (.inl ()) := by
  refine ⟨identityVariableEdges,⟨⟨identity_binding.labelling identityNet,?_⟩,rfl,⟨.var,rfl⟩⟩⟩
  exact .node (.inl ()) (.inl ()) lamBody rfl rfl ⟨rfl,rfl⟩
    (identityBindingLoop 0 Context.empty Context.empty).forward

/-- A full Def.3.5.13 matching fixture, constructed from raw actual paths and
unique binder suffixes rather than assumed source-correctness certificates. -/
theorem identity_matches : Matches identityNet (.inl ()) (.lam (.var 0)) := by
  apply encode_matches_of_access_classification (.lam (.var 0)) 0
  · intro es
    rcases identity_access_cases es with h | h
    · refine ⟨.lam (.var 0),?_,?_⟩
      · rw [h]; rfl
      · rw [h]; exact ⟨rfl,True.intro⟩
    · refine ⟨.var 0,?_,?_⟩
      · rw [h]; rfl
      · rw [h]
        exact ⟨rfl,identity_binding,identity_binding_index⟩
  · rintro ⟨path,hp⟩
    cases path with
    | nil => exact ⟨identityRootAccess,rfl⟩
    | cons s path =>
      cases s with
      | fn => simp [subtermAt] at hp
      | arg => simp [subtermAt] at hp
      | body =>
        cases path with
        | nil => exact ⟨identityVariableAccess,rfl⟩
        | cons s path => cases s <;> simp [subtermAt] at hp

example : ¬Matches identityNet (.inl ()) (.lam (.var 1)) := by
  intro h
  have same := identity_matches.unique h
  cases same
/-- Binding and shape cannot be replaced by physical-node or endpoint equality. -/
example : syntaxShape (.var 0) ≠ syntaxShape (.var 1) := by decide
example : (Term.lam (.lam (.var 0))) ≠ (.lam (.lam (.var 1))) := by decide
example : portKind (.op .lam) lamBody = none := rfl
example : portKind (.op .app) appArg = none := rfl
example : portKind (.op .fan) fanO = none := rfl
example : accessKind identityNet [] = none := rfl

/-- Two individually valid terminal observations cannot assign different binders. -/
example (es : List (Endpoint identityNet)) :
    Observes identityNet es (.var 0) → ¬Observes identityNet es (.var 1) := by
  intro h h'
  have := Observes.unique identityNet h h'
  cases this

#print axioms identity_matches
#print axioms Matches.unique
#print axioms BindingSuffix.labelling
end Lamping.Checks.Soundness


namespace Lamping.Checks.SoundnessPrefix
open AG Graph
inductive Node where
  | app | lam | cro | dead
  deriving DecidableEq
instance : FiniteNames Node := ⟨[.app,.lam,.cro,.dead], by intro n; cases n <;> simp⟩
def labels : Node → Label signature
  | .app => label .app 0 | .lam => label .lam 0
  | .cro => label .cro 0 | .dead => garbage

def net : Net signature Node Unit Empty where
  label := labels
  wire := {
    mate := fun e => match e with
      | .inl ⟨.app,.inl ()⟩ => .inl ⟨.lam,.inl ()⟩
      | .inl ⟨.app,.inr false⟩ => .inr (.inl ())
      | .inl ⟨.app,.inr true⟩ => .inl ⟨.dead,()⟩
      | .inl ⟨.lam,.inl ()⟩ => .inl ⟨.app,.inl ()⟩
      | .inl ⟨.lam,.inr false⟩ => .inl ⟨.cro,.inl ()⟩
      | .inl ⟨.lam,.inr true⟩ => .inl ⟨.cro,.inr ()⟩
      | .inl ⟨.cro,.inl ()⟩ => .inl ⟨.lam,.inr false⟩
      | .inl ⟨.cro,.inr ()⟩ => .inl ⟨.lam,.inr true⟩
      | .inl ⟨.dead,()⟩ => .inl ⟨.app,.inr true⟩
      | .inr (.inl ()) => .inl ⟨.app,.inr false⟩
      | .inr (.inr ⟨e,_⟩) => nomatch e
    involutive := by
      rintro (⟨n,p⟩ | (u | ⟨e,d⟩))
      · cases n <;> cases p <;> first | rfl | rename_i q; cases q <;> rfl
      · cases u; rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨n,p⟩ | (u | ⟨e,d⟩))
      · cases n <;> cases p <;> first | (intro h; cases h) | rename_i q; cases q <;> (intro h; cases h)
      · intro h; cases h
      · exact nomatch e }

def edge : BetaEdge net where
  app := .app
  lam := .lam
  index := 0
  appLabel := rfl
  lamLabel := rfl
  appFun := .inl ()
  appCtx := .inr false
  appArg := .inr true
  lamCtx := .inl ()
  lamBody := .inr true
  lamBind := .inr false
  appFun_role := HEq.rfl
  appCtx_role := HEq.rfl
  appArg_role := HEq.rfl
  lamCtx_role := HEq.rfl
  lamBody_role := HEq.rfl
  lamBind_role := HEq.rfl
  principal := [.inl ⟨.app,.inl ()⟩]
  principalStart := rfl
  principalEnd := rfl
  transparent := by simp

def loop : BindingLoop net [.inl ⟨.lam,lamBody⟩,.inl ⟨.cro,.inl ()⟩]
    Context.empty Context.empty where
  binder := .lam
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := .cons (LabelledTurn.node (g:=net) Node.cro (.inr ()) (.inl ()) (by
    simpa using Traversal.direct (Passage.cro (i:=0) Context.empty Context.empty))) (.single _ _)
  forward := .node .cro (.inr ()) (.inl ()) rfl rfl True.intro (.single _)
  shell := by intro k hk; change k < 0 at hk; omega

def full : List (Endpoint net) := [.inr (.inl ()),.inl ⟨.app,.inl ()⟩,
  .inl ⟨.lam,lamBody⟩,.inl ⟨.cro,.inl ()⟩,.inl ⟨.lam,.inl ()⟩,.inl ⟨.app,appArg⟩]
def cut : List (Endpoint net) := full.take 5

theorem full_generated : ExpandedProperPath net () full := by
  have arg : ForwardProperPath net [.inr (.inl ()),.inl ⟨.app,appArg⟩] := by
    refine ⟨⟨Context.empty,Context.empty,?_⟩,?_⟩
    · exact .cons (LabelledTurn.node (g:=net) Node.app appCtx appArg (.direct (.appArg _))) (.single _ _)
    · exact .node .app appCtx appArg rfl rfl ⟨rfl,Or.inr rfl⟩ (.single _)
  have body : ForwardProperPath net [.inr (.inl ()),.inl ⟨.app,.inl ()⟩,
      .inl ⟨.lam,lamBody⟩,.inl ⟨.cro,.inl ()⟩] := by
    refine ⟨⟨Context.empty,Context.empty,?_⟩,?_⟩
    · exact .cons (LabelledTurn.node (g:=net) Node.app appCtx (.inl ()) (.direct (.appFun _)))
        (.cons (LabelledTurn.node (g:=net) Node.lam (.inl ()) lamBody (.direct (.lamBody _))) loop.proper)
    · exact .node .app appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩
        (Forward.node (g:=net) Node.lam (.inl ()) lamBody rfl rfl ⟨rfl,rfl⟩ loop.forward)
  exact ExpandedProperPath.insert edge [.inr (.inl ())] _ []
    (.base arg rfl) (.base body rfl) rfl rfl rfl _ _ loop rfl

theorem loops_length (es : List (Endpoint net)) (a b : Context) (h : BindingLoop net es a b) :
    2 ≤ es.length := by
  rcases h with ⟨n,isLam,body,bind,hbody,hbind,start,finish,proper,forward,shell⟩
  cases n with
  | app => cases isLam
  | cro => cases isLam
  | dead => cases isLam
  | lam =>
    have hb : body=lamBody := eq_of_heq hbody
    have hv : bind=lamBind := eq_of_heq hbind
    subst body; subst bind
    obtain ⟨tail,ht⟩ := List.head?_eq_some_iff.mp start
    cases tail with
    | nil =>
      rw [ht] at finish
      change some (Sum.inl ⟨Node.lam,lamBody⟩ : Endpoint net) =
        some (Sum.inl ⟨Node.cro,Sum.inl ()⟩) at finish
      cases finish
    | cons e tail => simp [ht]

theorem cut_not_forward : ¬Forward net cut := by
  intro h
  change Forward net [.inr (.inl ()),.inl ⟨.app,.inl ()⟩,
    .inl ⟨.lam,lamBody⟩,.inl ⟨.cro,.inl ()⟩,.inl ⟨.lam,.inl ()⟩] at h
  cases h with
  | node n p q ha hl hd hs =>
    cases ha; cases hl
    cases hs with
    | node n p q ha hl hd hs =>
      cases ha; cases hl
      cases hs with
      | node n p q ha hl hd hs =>
        cases ha; cases hl
        cases hs with
        | node n p q ha hl hd hs =>
          cases ha; cases hl
          exact (by cases hd.1 : False)
        | transparent w => exact nomatch w
      | transparent w => exact nomatch w
    | transparent w => exact nomatch w
  | transparent w => exact nomatch w

theorem cut_not_generated : ¬ExpandedProperPath net () cut := by
  intro h
  exact cut_not_forward (h.short_is_ordinary loops_length (by decide)).2

example : full.take 5 = cut := rfl

theorem cut_in_prefixClosure : PrefixExpandedProperPath (g:=net) () cut := by
  refine ⟨(by intro h; have hh := congrArg List.length h; change 5=0 at hh; omega),[.inl ⟨.app,appArg⟩],?_⟩
  exact full_generated

/-- The new nonempty-prefix closure strictly includes the old physical-list
relation. The graph is literal and finite; encode-reachability is not asserted. -/
example : ∃ es, PrefixExpandedProperPath (g:=net) () es ∧ ¬ExpandedProperPath net () es :=
  ⟨cut,cut_in_prefixClosure,cut_not_generated⟩

#print axioms cut_not_generated
#print axioms PrefixExpandedProperPath.least
end Lamping.Checks.SoundnessPrefix













namespace Lamping.Checks.SoundnessPartialInput
open AG Graph Lambda
abbrev graph := varNet 0 0
abbrev inputBoundary : Boundary (.var 0) := .inr ⟨0,rfl⟩
def edges : List (Endpoint graph) :=
  [.inr (.inl inputBoundary),.inl ⟨(),.inr ()⟩]

/-- No proper operator exists here, so the three old ordinary properties hold.
This is an explicit generic-API countercheck, not an encode-closed graph. -/
theorem ordinary_properties : OrdinaryPathInvariants graph inputBoundary := by
  have noContextRole : ∀ (x : Endpoint graph) role index,
      (role=.appCtx ∨ role=.lamCtx) → ¬AtProperRole graph inputBoundary x role index := by
    intro x role index ctx atRole
    cases atRole with
    | root => rcases ctx with h|h <;> cases h
    | appCtx n p i lab role => cases lab
    | appFun n p i lab role => cases lab
    | appArg n p i lab role => cases lab
    | lamCtx n p i lab role => cases lab
    | lamBody n p i lab role => cases lab
    | lamBind n p i lab role => cases lab
  constructor
  · intro es e f sr tr m n a b start finish source outgoing target incoming fw labels
    cases target with
    | root => exact False.elim incoming
    | appCtx n p i lab role => cases lab
    | appFun n p i lab role => cases lab
    | appArg n p i lab role => cases lab
    | lamCtx n p i lab role => cases lab
    | lamBody n p i lab role => cases lab
    | lamBind n p i lab role => cases lab
  · intro es cs trace rooted fw i j e a b n role lt atI atJ csI csJ ctx atRole
    exact False.elim (noContextRole _ _ _ ctx atRole)
  · intro es a b n ctx body bind isLam
    cases n
    cases isLam

private def CroPrincipalEmpty (i : Nat) : (k : Kind) → Port k → Context → Prop
  | .op .cro,.inl _,a => a.get i=.empty
  | _,_,_ => True
private theorem cro_input_empty {i k p q a b} (h : Traversal i k p q a b) :
    CroPrincipalEmpty i k p a := by
  cases h with
  | direct hp => cases hp <;> trivial
  | inverse hp =>
    cases hp <;> simp [CroPrincipalEmpty,Context.replace,Context.cons]

theorem proper : ForwardProperPath graph edges := by
  constructor
  · refine ⟨Context.empty,Context.empty,?_⟩
    apply Labelling.cons
    · exact LabelledTurn.node (g:=graph) () (.inl ()) (.inr ())
        (.inverse (by simpa using Passage.cro (i:=0) Context.empty Context.empty))
    · exact .single _ _
  · exact .node () (.inl ()) (.inr ()) rfl rfl True.intro (.single _)

/-- Some context exists, but this genuine inverse-Cro path cannot take a
star head. Thus proper-terminal restrictions must not be erased. -/
theorem no_star_input : ¬∃ output,
    Labelling graph edges (Context.empty.cons (.star .empty)) output := by
  rintro ⟨output,h⟩
  cases h with
  | cons turn tail =>
    cases turn with
    | node n p q rule =>
      have wrong := cro_input_empty rule
      change Level.star .empty = Level.empty at wrong
      cases wrong

example : GeneratedExpandedProperPath graph inputBoundary edges :=
  .base proper rfl
example : ¬(∀ input : Context, ∃ output, Labelling graph edges input output) := by
  intro h
  exact no_star_input (h (Context.empty.cons (.star .empty)))

#print axioms Traversal.output_unique
#print axioms ExpandedContextTrace.input_unique
#print axioms ExpandedIndependence.root_input
end Lamping.Checks.SoundnessPartialInput


namespace Lamping.Checks.SoundnessMarkers
open AG Graph AG.Marker

/-- Equal erased constructors do not identify their writer histories. -/
example : (TaggedLevel.o (.input 0 []) .empty).erase =
    (TaggedLevel.o (.written 0) .empty).erase := rfl
example : TaggedLevel.o (.input 0 []) .empty ≠ TaggedLevel.o (.written 0) .empty := by decide
example (a : Context) (event : Nat) :
    ¬TaggedContext.HasOrigin (.written event) (TaggedContext.initial a) :=
  TaggedContext.initial_no_written a event

abbrev emptyTags := TaggedContext.initial Context.empty
abbrev before := emptyTags.replace 0 (emptyTags.cons .empty)
abbrev after := emptyTags.replace 0 (emptyTags.cons (.o (.written 0) .empty))

example : TaggedTraversal 0 0 (.op .fan) fanO (.inl ()) before after :=
  .direct (.fanO emptyTags emptyTags .empty)
/-- Event1 consumes the constructor really created by event0. Requiring its
origin to be event1 would reject this actual cancellation. -/
example : TaggedTraversal 1 0 (.op .fan) (.inl ()) fanO after before :=
  .inverse (.written 0) (.fanO emptyTags emptyTags .empty)
example : TaggedContext.HasOrigin (.written 0) after := by
  apply (TaggedContext.hasOrigin_replace _ _ _ _).mpr
  exact Or.inr ((TaggedContext.hasOrigin_cons _ _ _).mpr (Or.inl (by simp [TaggedLevel.origins])))
example : ¬TaggedContext.HasOrigin (.written 1) after := by
  simp only [TaggedContext.hasOrigin_replace,TaggedContext.hasOrigin_cons,TaggedLevel.origins,
    List.mem_cons,List.not_mem_nil]
  rintro (⟨k,hk,_⟩ | ((same | impossible) | old))
  · omega
  · have eq := Origin.written.inj same
    omega
  · exact impossible
  · exact TaggedContext.initial_no_written Context.empty 1 old

def fanOutput : Context := Context.empty.cons (.o .empty)
def actualFanPath : LocalPath (leftNet .fan .app 0 1) (.inl false) (.inr false)
    Context.empty fanOutput :=
  leftRoutePath .fan .app 0 1 false false Context.empty fanOutput fanOutput
    (by simpa [fanOutput] using Traversal.direct (Passage.fanO (i:=0) Context.empty Context.empty .empty))
    (.inverse (.appFun fanOutput))

example : ∃ output, TaggedLabelling (leftNet .fan .app 0 1) 0 actualFanPath.edges
      (TaggedContext.initial Context.empty) output ∧ output.erase=fanOutput ∧
      ∀ event, TaggedContext.HasOrigin (.written event) output → WriterAt event 0 actualFanPath.edges :=
  actual_writer_attribution actualFanPath.labeling

#print axioms liftTraversal
#print axioms actual_writer_attribution
#print axioms WriterAt.position
/-- A surviving old Star really crosses a writing fan and an application.
Replaying the empty word removes that old Star while retaining the fan's O. -/
abbrev oldInput := emptyTags.cons (.star (.input 0 []) .empty)
abbrev oldOutput := emptyTags.cons (.o (.written 0) (.star (.input 0 []) .empty))

theorem oldCrossing : TaggedLabelling (leftNet .fan .app 0 1) 0
    (leftRoute .fan .app 0 1 false false) oldInput oldOutput := by
  refine TaggedLabelling.cons (b:=oldOutput) (TaggedTurn.node (g:=leftNet .fan .app 0 1) (.inl ()) (.inr false) (.inl ()) ?_) ?_
  · simpa [oldInput,oldOutput,TaggedContext.replace] using
      TaggedTraversal.direct (TaggedPassage.fanO (i:=0) emptyTags emptyTags
        (.star (.input 0 []) .empty))
  · exact .cons (TaggedTurn.node (g:=leftNet .fan .app 0 1) (.inr ()) (.inl ()) (.inr false) (.inverse (.written 1) (.appFun oldOutput)))
      (.single 2 _ oldOutput)

theorem oldCrossing_replay (xs : List Bool) :
    Labelling (leftNet .fan .app 0 1) (leftRoute .fan .app 0 1 false false)
      (TaggedContext.rewrite (.input 0 []) xs oldInput).erase
      (TaggedContext.rewrite (.input 0 []) xs oldOutput).erase := by
  have initEq : oldInput=TaggedContext.initial (Context.empty.cons (.star .empty)) := by
    ext k
    cases k <;> rfl
  apply TaggedLabelling.erase
  apply oldCrossing.rewrite_old 0 [] xs
  · rw [initEq]
    exact TaggedContext.initial_unique _
  · rw [initEq]
    exact TaggedContext.initial_originsBefore _
  · exact ⟨0,by simp [oldOutput,TaggedContext.cons,TaggedLevel.origins]⟩

example : (TaggedContext.rewrite (.input 0 []) [] oldInput).erase=Context.empty := by
  ext k
  cases k <;> rfl
example : (TaggedContext.rewrite (.input 0 []) [] oldOutput).erase=fanOutput := by
  ext k
  cases k <;> rfl
example : (TaggedContext.rewrite (.input 0 []) [false,true] oldOutput).erase.get 0=
    .o (.o (.star .empty)) := rfl

/-- Duplication is rejected on finite support, without an infinite count sum. -/
example : ¬UniqueOrigins (emptyTags.cons
    (.pair (.written 0) (.o (.input 0 []) .empty) (.star (.input 0 []) .empty))) := by
  intro h
  have wrong := h (.input 0 []) 1
  change 2≤1 at wrong
  omega

/-- The emitted outer O cannot be changed to Star by choosing another input. -/
example {input output : Context}
    (labels : Labelling (leftNet .fan .app 0 1) (leftRoute .fan .app 0 1 false false) input output) :
    levelMarkerAt [] (output.get 0)=some .o := by
  have initialEq : oldInput=TaggedContext.initial (Context.empty.cons (.star .empty)) := by
    ext k
    cases k <;> rfl
  have tagged := oldCrossing
  rw [initialEq] at tagged
  exact written_marker_fixed tagged 0 [] 0 .o rfl labels

example : ¬∃ input : Context,
    Labelling (leftNet .fan .app 0 1) (leftRoute .fan .app 0 1 false false)
      input (Context.empty.cons (.star .empty)) := by
  rintro ⟨input,labels⟩
  have initialEq : oldInput=TaggedContext.initial (Context.empty.cons (.star .empty)) := by
    ext k
    cases k <;> rfl
  have tagged := oldCrossing
  rw [initialEq] at tagged
  have wrong := written_marker_fixed tagged 0 [] 0 .o rfl labels
  cases wrong

/-- A concrete generated detour crosses both actual reverse-beta seams.
The old input Star survives the Cro level shift and both identity turns. -/
abbrev reverseOutput := oldInput.cons .empty
 theorem reverseCrossing : TaggedExpandedLabelling SoundnessPrefix.net 0 SoundnessPrefix.full oldInput reverseOutput := by
  have first : TaggedExpandedTurn SoundnessPrefix.net 0
      (SoundnessPrefix.net.wire (.inr (.inl ()))) (.inl ⟨.app,.inl ()⟩) oldInput oldInput :=
    .ordinary (TaggedTurn.node (g:=SoundnessPrefix.net) .app appCtx (.inl ()) (.direct (.appFun oldInput)))
  have second : TaggedExpandedTurn SoundnessPrefix.net 1
      (SoundnessPrefix.net.wire (.inl ⟨.app,.inl ()⟩)) (.inl ⟨.lam,lamBody⟩) oldInput oldInput :=
    .ordinary (TaggedTurn.node (g:=SoundnessPrefix.net) .lam (.inl ()) lamBody (.direct (.lamBody oldInput)))
  have third : TaggedExpandedTurn SoundnessPrefix.net 2
      (SoundnessPrefix.net.wire (.inl ⟨.lam,lamBody⟩)) (.inl ⟨.cro,.inl ()⟩) oldInput reverseOutput := by
    apply TaggedExpandedTurn.ordinary
    apply TaggedTurn.node (g:=SoundnessPrefix.net) SoundnessPrefix.Node.cro (.inr ()) (.inl ())
    simpa [reverseOutput,TaggedContext.replace] using
      TaggedTraversal.direct (TaggedPassage.cro (i:=0) (origin:=.written 2) emptyTags oldInput)
  exact .cons first (.cons second (.cons third
    (.cons (.bindToCtx SoundnessPrefix.edge reverseOutput)
      (.cons (.funToArg SoundnessPrefix.edge reverseOutput) (.single 5 _ reverseOutput)))))

example (xs : List Bool) :
    ExpandedLabelling SoundnessPrefix.net SoundnessPrefix.full
      (TaggedContext.rewrite (.input 0 []) xs oldInput).erase
      (TaggedContext.rewrite (.input 0 []) xs reverseOutput).erase := by
  have initialEq : oldInput=TaggedContext.initial (Context.empty.cons (.star .empty)) := by
    ext k
    cases k <;> rfl
  apply TaggedExpandedLabelling.erase
  apply reverseCrossing.rewrite_old SoundnessPrefix.net 0 [] xs
  · rw [initialEq]; exact TaggedContext.initial_unique _
  · rw [initialEq]; exact TaggedContext.initial_originsBefore _
  · exact ⟨1,by simp [reverseOutput,oldInput,TaggedContext.cons,TaggedLevel.origins]⟩

example : (TaggedContext.rewrite (.input 0 []) [] reverseOutput).erase=Context.empty := by
  ext k
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

#print axioms reverseCrossing
#print axioms expanded_old_marker_replay
#print axioms expanded_written_marker_fixed
#print axioms expanded_no_written_terminal_tail
#print axioms written_marker_fixed
#print axioms free_tail_no_written
#print axioms no_written_terminal_tail
#print axioms actual_path_no_copy
#print axioms old_marker_replay
#print axioms oldCrossing_replay
end Lamping.Checks.SoundnessMarkers










namespace Lamping.Checks.SoundnessOrdinaryBase
open AG Graph
/-- This is the actual encoded I I beta edge with one transparent W. -/
example : Paths.encodedBetaOccurrence.principal.length=2 := rfl
example : Paths.encodedBetaOccurrence.reverseRoute.length=2 := rfl
example (es : List (Endpoint actualBetaSite.net)) (fw : Forward actualBetaSite.net es)
    (rooted : es.head?=some (.inr (.inl (.inl ())))) :
    es.getLast?≠some (actualBetaSite.net.wire Paths.encodedBetaOccurrence.funEnd) := by
  exact fw.no_reversed_target rooted Paths.encodedBetaOccurrence

/-- The same physical subdivided edge does support the intended expanded
backward passage; exclusion concerns ordinary rooted Forward paths. -/
example (a : Context) : ExpandedLabelling actualBetaSite.net Paths.encodedBetaOccurrence.backwardPiece a a :=
  Paths.encodedBetaOccurrence.backward_piece_labeling a

example (a : Context) : ConstantLabelling (g:=actualBetaSite.net) a
    (Paths.encodedBetaOccurrence.reverseRoute.take 1) := by
  have all := Paths.encodedBetaOccurrence.reverse_constant_labelling a
  have split : Paths.encodedBetaOccurrence.reverseRoute=
      Paths.encodedBetaOccurrence.reverseRoute.take 1 ++ Paths.encodedBetaOccurrence.reverseRoute.drop 1 :=
    (List.take_append_drop _ _).symm
  rw [split] at all
  exact all.prefix (by
    intro empty
    have wrong := congrArg List.length empty
    change 1=0 at wrong
    omega)

/-- The five-segment prefix that the old bare grammar misses really inherits
a label from its body via the actual reversed beta seam. -/
example : ExpandedLabelling SoundnessPrefix.net SoundnessPrefix.cut Context.empty Context.empty := by
  have body : ExpandedLabelling SoundnessPrefix.net
      ([.inr (.inl ())]++SoundnessPrefix.edge.principal++
        [.inl ⟨.lam,lamBody⟩,.inl ⟨.cro,.inl ()⟩]) Context.empty Context.empty := by
    apply Labelling.expanded
    exact .cons (LabelledTurn.node (g:=SoundnessPrefix.net) .app appCtx (.inl ()) (.direct (.appFun _)))
      (.cons (LabelledTurn.node (g:=SoundnessPrefix.net) .lam (.inl ()) lamBody (.direct (.lamBody _)))
        SoundnessPrefix.loop.proper)
  exact SoundnessPrefix.edge.insert_reverse_prefix_labeling [.inr (.inl ())]
    [.inl ⟨.lam,lamBody⟩,.inl ⟨.cro,.inl ()⟩] [.inl ⟨.lam,.inl ()⟩] [] rfl body rfl

example : ∃ cs,ExpandedContextTrace SoundnessPrefix.net SoundnessPrefix.full cs ∧
    cs[1]?=some SoundnessMarkers.oldInput.erase := by
  obtain ⟨cs,trace,head,last⟩ := (SoundnessMarkers.reverseCrossing.erase SoundnessPrefix.net).contextTrace SoundnessPrefix.net
  refine ⟨cs,trace,?_⟩
  have first : ExpandedLabelling SoundnessPrefix.net
      [.inr (.inl ()),.inl ⟨.app,.inl ()⟩]
      SoundnessMarkers.oldInput.erase SoundnessMarkers.oldInput.erase :=
    .cons (.ordinary (LabelledTurn.node (g:=SoundnessPrefix.net) .app appCtx (.inl ()) (.direct (.appFun _)))) (.single _ _)
  exact trace.labelled_prefix_point head
    (show SoundnessPrefix.full=[.inr (.inl ()),.inl ⟨.app,.inl ()⟩] ++
      [.inl ⟨.lam,lamBody⟩,.inl ⟨.cro,.inl ()⟩,.inl ⟨.lam,.inl ()⟩,.inl ⟨.app,appArg⟩] from rfl)
    (by intro empty; cases empty) first

#print axioms ExpandedContextTrace.labelled_prefix_point
#print axioms ExpandedNesting.binding_prefix_unique
#print axioms ConstantLabelling.reverse
#print axioms BetaEdge.insert_reverse_prefix_labeling
#print axioms BetaEdge.insert_with_argument_independence
#print axioms Independence.expanded_ordinary_prefix_base
#print axioms Forward.transparent_predecessor
#print axioms Forward.no_reverse_transparent
#print axioms Forward.no_reversed_target
#print axioms Independence.rooted_proper_occurrence
#print axioms Independence.expanded_ordinary_base
end Lamping.Checks.SoundnessOrdinaryBase




namespace Lamping.Checks.SoundnessAssignmentBoundary
open AG Graph
/-- This synthetic graph is an assignment-boundary check. It is not asserted
to have root Transparency or to be a reachable closed encoding. -/
def labels : Bool → Label signature | false => label .lam 1 | true => label .cro 0
def graph : Net signature Bool Unit Empty where
  label := labels
  wire := {
    mate := fun e => match e with
      | .inl ⟨false,.inl ()⟩ => .inr (.inl ())
      | .inl ⟨false,.inr false⟩ => .inl ⟨true,.inl ()⟩
      | .inl ⟨false,.inr true⟩ => .inl ⟨true,.inr ()⟩
      | .inl ⟨true,.inl ()⟩ => .inl ⟨false,.inr false⟩
      | .inl ⟨true,.inr ()⟩ => .inl ⟨false,.inr true⟩
      | .inr (.inl ()) => .inl ⟨false,.inl ()⟩
      | .inr (.inr ⟨w,_⟩) => nomatch w
    involutive := by
      rintro (⟨node,port⟩ | (boundary | ⟨w,d⟩))
      · cases node <;> cases port <;> first | rfl | rename_i bit; cases bit <;> rfl
      · cases boundary; rfl
      · exact nomatch w
    fixedPointFree := by
      rintro (⟨node,port⟩ | (boundary | ⟨w,d⟩))
      · cases node <;> cases port <;> first | (intro impossible; cases impossible) | rename_i bit; cases bit <;> (intro impossible; cases impossible)
      · intro impossible; cases impossible
      · exact nomatch w }

def edges : List (Endpoint graph) := [.inl ⟨false,lamBody⟩,.inl ⟨true,.inl ()⟩]
def emptyBinding : BindingLoop graph edges Context.empty Context.empty where
  binder := false
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := .cons (LabelledTurn.node (g:=graph) true (.inr ()) (.inl ())
    (.direct (by simpa using Passage.cro (i:=0) Context.empty Context.empty))) (.single _ _)
  forward := .node true (.inr ()) (.inl ()) rfl rfl True.intro (.single _)
  shell := by intro k _; rfl

def starInput : Context := Context.empty.cons (.star .empty)
def shiftedOutput : Context := starInput.cons .empty
 theorem changed_assignment : Labelling graph edges starInput shiftedOutput :=
  .cons (LabelledTurn.node (g:=graph) true (.inr ()) (.inl ())
    (.direct (by simpa [shiftedOutput] using Passage.cro (i:=0) Context.empty starInput))) (.single _ _)
 theorem changed_assignment_not_binding : ¬Context.SameShell 1 starInput shiftedOutput := by
  intro shell
  have impossible := shell 0 (by omega)
  cases impossible

/-- Thus the independent BindingLoop witness cannot supply a shell equality
for arbitrary label assignments on the same literal physical loop. -/
example : Nonempty (BindingLoop graph edges Context.empty Context.empty) ∧
    Labelling graph edges starInput shiftedOutput ∧¬Context.SameShell 1 starInput shiftedOutput :=
  ⟨⟨emptyBinding⟩,changed_assignment,changed_assignment_not_binding⟩
#print axioms changed_assignment
#print axioms changed_assignment_not_binding
end Lamping.Checks.SoundnessAssignmentBoundary


namespace Lamping.Checks.SoundnessInitialInsertion
open AG Graph Lambda

def edge (n : Nat) : BetaEdge (encode n identityApp).net where
  app := .inl (.inl ())
  lam := .inr (.inl (.inl ()))
  index := n
  appLabel := rfl
  lamLabel := rfl
  appFun := .inl ()
  appCtx := .inr false
  appArg := .inr true
  lamCtx := .inl ()
  lamBody := .inr true
  lamBind := .inr false
  appFun_role := HEq.rfl
  appCtx_role := HEq.rfl
  appArg_role := HEq.rfl
  lamCtx_role := HEq.rfl
  lamBody_role := HEq.rfl
  lamBind_role := HEq.rfl
  principal := [.inl ⟨.inl (.inl ()),.inl ()⟩,.inr (.inr (.inr (.inl (.inl ())),true))]
  principalStart := rfl
  principalEnd := rfl
  transparent := by
    intro e f pair
    change (e,f)∈[(Sum.inl ⟨Sum.inl (Sum.inl ()),Sum.inl ()⟩,
      Sum.inr (Sum.inr (Sum.inr (Sum.inl (Sum.inl ())),true)))] at pair
    rcases List.mem_singleton.mp pair with same
    cases same
    exact ⟨.inr (.inl (.inl ())),false,rfl,rfl⟩

abbrev shell := Context.empty.cons (.star .empty)
abbrev tail := Context.empty.cons (.o .empty)
abbrev input (n : Nat) := shell.replace n tail
abbrev output (n : Nat) := shell.replace n (tail.cons .empty)
abbrev childEdges (n : Nat) : List (Endpoint (encode n identity).net) :=
  [.inl ⟨.inl (),lamBody⟩,.inr (.inr (.inr (.inl ()),true)),
   .inl ⟨.inr (),.inl ()⟩,.inr (.inr (.inr (.inr ⟨0,rfl⟩),false))]
def loopEdges (n : Nat) : List (Endpoint (encode n identityApp).net) :=
  ((childEdges n).map (InitialOffsets.unionL (encode n identity).net (encode (n+1) identity).net)).map
    (plugRight (appPatch n identity identity) (unionNet (encode n identity).net (encode (n+1) identity).net))
def actualLoop (n : Nat) : InitialOffsets.RawLoop (encode n identityApp).net (loopEdges n) (input n) (output n) :=
  (((identityBindingLoop n shell tail).rawLoop).unionLeft (encode n identity).net (encode (n+1) identity).net).plugRight
    (appPatch n identity identity) (unionNet (encode n identity).net (encode (n+1) identity).net)

example : (edge 3).principal.length=2 := rfl
example : (input 3).get 0=.star .empty := rfl
example : (output 3).get 0=.star .empty := rfl
example : (input 3).get 3=.o .empty := rfl
example : (output 3).get 3=.empty := rfl
example : (output 3).get 4=.o .empty := rfl
abbrev pre (n : Nat) : List (Endpoint (encode n identityApp).net) := [.inr (.inl (.inl ()))]
abbrev argumentW (n : Nat) : (encode n identityApp).W := .inr (.inr (.inl ()))
abbrev suffix (n : Nat) : List (Endpoint (encode n identityApp).net) := [.inr (.inr (argumentW n,true))]
abbrev argument (n : Nat) := pre n ++ (edge n).argEnd::suffix n

def argumentTrace (n : Nat) : ExpandedContextTrace (encode n identityApp).net (argument n)
    [input n,input n,input n] :=
  .cons (.ordinary ((edge n).app_arg_turn (input n)))
    (.cons (.ordinary (.transparent (argumentW n) false (input n))) (.single _ _))
def argumentForward (n : Nat) : Forward (encode n identityApp).net (argument n) :=
  .node (.inl (.inl ())) appCtx appArg rfl rfl ⟨rfl,Or.inr rfl⟩
    (.transparent (argumentW n) false rfl rfl (.single _))

def bodyLabels (n : Nat) : ExpandedLabelling (encode n identityApp).net
    (pre n ++ (edge n).principal ++ loopEdges n) (input n) (output n) :=
  (edge n).body_with_loop_labeling (pre n) (loopEdges n) (.single _ _) rfl
    (actualLoop n).start (actualLoop n).proper.expanded

/-- A level3 initial redex preserves its real Star shell while moving the
higher O from level3 to level4 along the actual loop. -/
theorem actual_shell : Context.SameShell 3 (input 3) (output 3) :=
  encode_insert_actual_shell identityApp 3 (edge 3) (pre 3) (loopEdges 3) (suffix 3)
    _ (argumentTrace 3) rfl rfl rfl (actualLoop 3).start (actualLoop 3).finish
    (InitialOffsets.encode_rawLoop_binding identityApp 3 _ _ _ (actualLoop 3)).forward (bodyLabels 3)

abbrev inserted (n : Nat) := pre n ++ (edge n).principal ++ loopEdges n ++ (edge n).reverseRoute ++ [(edge n).argEnd] ++ suffix n
 theorem nonzero_insert_exists : ∃ result,ExpandedLabelling (encode 3 identityApp).net (inserted 3) (input 3) result := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have indep := (encode_closed_independence identityApp closed 3).expanded_ordinary_base rfl (argumentForward 3)
  exact encode_insert_labelable identityApp 3 (edge 3) (pre 3) (loopEdges 3) (suffix 3) indep
    _ (argumentTrace 3) rfl rfl rfl rfl (actualLoop 3).start (actualLoop 3).finish
    (InitialOffsets.encode_rawLoop_binding identityApp 3 _ _ _ (actualLoop 3)).forward (bodyLabels 3)
    (.inr (.inr (argumentW 3,true))) 4 rfl
    (.proper _ .lamCtx 4 (AtProperRole.lamCtx (g:=(encode 3 identityApp).net) (root:=.inl ()) (.inr (.inr (.inl ()))) (.inl ()) 4 rfl HEq.rfl) True.intro)

example : (inserted 3).length=11 := rfl
def bodyForward (n : Nat) : Forward (encode n identityApp).net
    (pre n ++ (edge n).principal ++ loopEdges n) :=
  .node (.inl (.inl ())) appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩
    (.transparent (.inr (.inl (.inl ()))) false rfl rfl
      (.node (.inr (.inl (.inl ()))) (.inl ()) lamBody rfl rfl ⟨rfl,rfl⟩
        (InitialOffsets.encode_rawLoop_binding identityApp n _ _ _ (actualLoop n)).forward))

def argumentLabels (n : Nat) (a : Context) : Labelling (encode n identityApp).net (argument n) a a :=
  .cons ((edge n).app_arg_turn a) (.cons (.transparent (argumentW n) false a) (.single _ _))

/-- Here the argument root is actually relabelled to output3, while the body
root remains input3. Both prefix contexts and the real loop shell agree. -/
theorem coherent_nonzero : CoherentExpandedCore (encode 3 identityApp).net (.inl ()) (inserted 3) (input 3) (output 3) := by
  apply CoherentExpandedCore.insert (edge 3) (pre 3) (loopEdges 3) (suffix 3)
    (argumentInput:=output 3) (seam:=input 3)
    (binding:=InitialOffsets.encode_rawLoop_binding identityApp 3 _ _ _ (actualLoop 3))
  · exact .base (argumentLabels 3 (output 3)) (argumentForward 3) rfl
  · exact .base ((bodyLabels 3).ordinary_of_forward _ (bodyForward 3)) (bodyForward 3) rfl
  · exact .single _ _
  · exact .single _ _
  · rfl
  · exact (actualLoop 3).start
  · exact (actualLoop 3).finish
  · rfl

example : input 3≠output 3 := by
  intro same
  have impossible := congrArg (fun c : Context => c.get 3) same
  cases impossible
example : ExpandedProperPath (encode 3 identityApp).net (.inl ()) (inserted 3) := coherent_nonzero.erase _
example : ExpandedLabelling (encode 3 identityApp).net (inserted 3) (input 3) (output 3) := coherent_nonzero.labelling _

 theorem coherent_cut : CoherentExpandedPrefix (encode 3 identityApp).net (.inl ()) ((inserted 3).take 8) (input 3) := by
  have full := coherent_nonzero.prefix (encode 3 identityApp).net
  rw [←List.take_append_drop 8 (inserted 3)] at full
  apply full.takePrefix
  intro empty
  have impossible := congrArg List.length empty
  change 8=0 at impossible
  omega
example : GeneratedExpandedProperPath (encode 3 identityApp).net (.inl ()) ((inserted 3).take 8) := coherent_cut.generated _
example : ∃ result,ExpandedLabelling (encode 3 identityApp).net ((inserted 3).take 8) (input 3) result := coherent_cut.labelling _

#print axioms CoherentExpandedCore.erase
#print axioms CoherentExpandedCore.labelling
#print axioms CoherentExpandedPrefix.generated
#print axioms CoherentExpandedPrefix.labelling
#print axioms coherent_nonzero
#print axioms coherent_cut
#print axioms BetaEdge.common_root_loop_labeling
#print axioms encode_insert_actual_shell
#print axioms encode_insert_labelable
#print axioms actual_shell
#print axioms nonzero_insert_exists
end Lamping.Checks.SoundnessInitialInsertion

namespace Lamping.Checks.SoundnessFlow
open AG Graph Lambda

def actionBoundary : Bool⊕Bool → Bool := Sum.elim (fun _ => false) (fun b => !b)
abbrev actionSchema : Schema := .fanAction .app 0 1 (by decide)

/-- A genuine action redex whose fan principal has negative polarity. Thus
fixing every control's principal to true would lose an actual schema instance. -/
def actionSourceFlow : FlowBalance actionSchema.left actionBoundary where
  nodes := fun _ => false
  vertices := Empty.elim
  wiring := by
    rintro (⟨u|u,p⟩ | ((a|b) | ⟨w,d⟩))
    · cases p <;> rfl
    · cases p <;> rfl
    · rfl
    · cases b <;> rfl
    · exact nomatch w

def actionTargetFlow : FlowBalance actionSchema.right.net actionBoundary :=
  fanRight_flow .app 0 1 false false actionBoundary (fun _ => rfl) (fun _ => rfl) rfl

example : actionTargetFlow.nodes (.inr false) = false := rfl
example : actionTargetFlow.nodes (.inr true) = true := rfl
example : ¬Nonempty (FlowBalance actionSchema.left (fun _ => true)) := by
  rintro ⟨flow⟩
  have impossible := flow.wiring (.inr (.inl (.inr true)))
  change true=false at impossible
  cases impossible

/-- An actual encoded root-to-variable path, including a gluing vertex and a
Cro, has positive departures under its real initial flow witness. -/
theorem identity_positive :
    ∃ flow : FlowBalance Soundness.identityNet initialBoundaryPolarity,
      ∀ e ∈ Soundness.identityVariableEdges,
        flowEndpoint Soundness.identityNet flow.nodes initialBoundaryPolarity flow.vertices e = true := by
  obtain ⟨flow⟩ := encode_flowBalance (.lam (.var 0)) 0
  obtain ⟨a,b,labels⟩ := Soundness.identity_binding.labelling Soundness.identityNet
  exact ⟨flow,labels.root_positive_departures flow (.inl ()) rfl rfl⟩

example (flow : FlowBalance actualBetaSite.net initialBoundaryPolarity)
    (es : List (Endpoint actualBetaSite.reduce)) (a b : Context)
    (labels : Labelling actualBetaSite.reduce es a b)
    (rooted : es.head? = some (.inr (.inl (.inl ())))) :
    (.inr (.inr (.inr (.inl true),true)) : Endpoint actualBetaSite.reduce) ∉ es :=
  actualBetaSite.beta_no_argument_entry flow (.inl ()) labels rooted rfl

#print axioms Schema.flow_preservation
#print axioms PathSite.principal_flow
#print axioms initial_trace_flowBalance
#print axioms PathSite.beta_no_argument_entry
#print axioms PathSite.beta_no_body_entry
#print axioms identity_positive
end Lamping.Checks.SoundnessFlow

namespace Lamping.Checks.SoundnessBetaAncestor
open AG Graph Lambda

private def identityPolarity : IdentityW → Bool
  | .inl (.inl e) | .inl (.inr e) => nomatch e
  | .inr (.inl _) => false
  | .inr (.inr _) => true

private def betaPolarity : BetaW⊕Unit → Bool
  | .inl (.inl (.inl w)) | .inl (.inl (.inr w)) => identityPolarity w
  | .inl (.inr _) | .inr _ => false

/-- The actual named encoding of I I, including both retained identity loops
and the transparent principal vertex, has an explicit source flow. -/
def actualFlow : FlowBalance actualBetaSite.net initialBoundaryPolarity where
  nodes := fun _ => true
  vertices := betaPolarity
  wiring := by
    rintro (⟨(u|(u|u))|(u|u),p⟩ | (b | ⟨w|v,d⟩))
    · cases p <;> rfl
    · cases p with | inl u => rfl | inr b => cases b <;> rfl
    · cases p <;> rfl
    · cases p with | inl u => rfl | inr b => cases b <;> rfl
    · cases p with | inl u => rfl | inr b => cases b <;> rfl
    · rcases b with u | x
      · rfl
      · have h := x.property
        change free identity x.val ∨ free identity x.val at h
        rcases h with h | h <;> exact False.elim (noIdentityFV ⟨x.val,h⟩)
    · rcases w with (w|w)|u
      · rcases w with (e|e)|(u|⟨k,h⟩)
        · exact nomatch e
        · exact nomatch e
        · cases d <;> rfl
        · change k=0 at h; subst k; cases d <;> rfl
      · rcases w with (e|e)|(u|⟨k,h⟩)
        · exact nomatch e
        · exact nomatch e
        · cases d <;> rfl
        · change k=0 at h; subst k; cases d <;> rfl
      · cases d <;> rfl
    · cases d <;> rfl

abbrev cut := cutFragment actualBetaSite.net (pathPartition (.beta 0) Unit) actualBetaSite.closed

private abbrev fnBody : (BetaW⊕Empty)⊕(Bool⊕Bool) :=
  .inl (.inl (.inl (.inl (.inr (.inl ())))))
private abbrev fnBinding : (BetaW⊕Empty)⊕(Bool⊕Bool) :=
  .inl (.inl (.inl (.inl (.inr (.inr ⟨0,rfl⟩)))))
private abbrev argumentWire : (BetaW⊕Empty)⊕(Bool⊕Bool) := .inl (.inl (.inr ()))

def reduced : List (Endpoint actualBetaSite.reduce) :=
  [.inr (.inl (.inl ())),
   .inr (.inr (.inr (.inl false),true)),
   .inr (.inr (.inr (.inr true),false)),
   .inr (.inr (fnBody,true)),
   .inl ⟨.inl (.inl ()),.inl ()⟩,
   .inr (.inr (fnBinding,false)),
   .inr (.inr (.inr (.inr false),true)),
   .inr (.inr (.inr (.inl true),false)),
   .inr (.inr (argumentWire,true))]

theorem reduced_labels (a : Context) : Labelling actualBetaSite.reduce reduced a (a.cons .empty) := by
  apply Labelling.cons (LabelledTurn.transparent (g:=actualBetaSite.reduce) (.inr (.inl false)) false _)
  apply Labelling.cons (LabelledTurn.transparent (g:=actualBetaSite.reduce) (.inr (.inr true)) true _)
  apply Labelling.cons (LabelledTurn.transparent (g:=actualBetaSite.reduce) fnBody false _)
  apply Labelling.cons (LabelledTurn.node (g:=actualBetaSite.reduce) (.inl (.inl ())) (.inr ()) (.inl ())
    (.direct (by simpa using Passage.cro (i:=0) Context.empty a)))
  apply Labelling.cons (LabelledTurn.transparent (g:=actualBetaSite.reduce) fnBinding true _)
  apply Labelling.cons (LabelledTurn.transparent (g:=actualBetaSite.reduce) (.inr (.inr false)) false _)
  apply Labelling.cons (LabelledTurn.transparent (g:=actualBetaSite.reduce) (.inr (.inl true)) true _)
  apply Labelling.cons (LabelledTurn.transparent (g:=actualBetaSite.reduce) argumentWire false _)
  exact .single _ _

abbrev lastOutside : Endpoint cut := .inr (.inr (.inr (),true))

/-- The literal encoded I I path crosses both beta reconnections and the
retained Cro. The general whole-path theorem, not a fixture-specific old
labelling, constructs an old ancestor with the same changing contexts. -/
theorem actual_ancestor (a : Context) :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net)),
      SiteBetaGeometry actualBetaSite edge ∧
      BetaPathResidual actualBetaSite edge (reduced.map (plugEnd _ _).invFun) old ∧
      ExpandedLabelling actualBetaSite.net old a (a.cons .empty) ∧
      old.head?=some (.inr (.inl (.inl ()))) ∧
      old.getLast?=some (actualBetaSite.outsideEnd lastOutside) :=
  actualBetaSite.beta_root_ancestor actualFlow (.inl ()) rfl (reduced_labels a) rfl lastOutside rfl

theorem actual_forward_ancestor (a : Context) :
    ∃ old : List (Endpoint actualBetaSite.net),
      ExpandedLabelling actualBetaSite.net old a (a.cons .empty) ∧
      ExpandedForward actualBetaSite.net old ∧
      old.head?=some (.inr (.inl (.inl ()))) ∧
      old.getLast?=some (actualBetaSite.outsideEnd lastOutside) := by
  obtain ⟨edge,old,geometry,relation,labels,forward,first,last⟩ :=
    actualBetaSite.beta_root_forward_ancestor actualFlow (.inl ()) rfl (reduced_labels a) rfl lastOutside rfl
  exact ⟨old,labels,forward,first,last⟩

theorem actual_stream (a : Context) :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net)) (count : Nat),
      BetaPathResidual actualBetaSite edge (reduced.map (plugEnd _ _).invFun) old ∧
      BetaDetourBlocks actualBetaSite.net old a (a.cons .empty) count ∧ 0<count := by
  obtain ⟨edge,old,geometry,relation,labels,first,last⟩ := actual_ancestor a
  obtain ⟨count,stream⟩ := relation.detour_blocks actualBetaSite geometry ((reduced_labels a).plug_decomposition _ _)
  have entry : (.inr (.inr (.inl (.inr false)))) ∈ reduced.map (plugEnd _ _).invFun := by
    exact List.mem_map.mpr ⟨.inr (.inr (.inr (.inr false),true)),by simp [reduced],rfl⟩
  have occurs := relation.reverse_occurs actualBetaSite entry
  exact ⟨edge,old,count,relation,stream,
    stream.positive_count actualBetaSite.net actualFlow (.inl ()) rfl first edge occurs⟩

theorem actual_first_backward (a : Context) :
    ∃ (edge : BetaEdge actualBetaSite.net) (pre tail : List (Endpoint actualBetaSite.net))
      (seam : Context) (remaining : Nat),
      Labelling actualBetaSite.net pre a seam ∧
      pre.getLast?=some (actualBetaSite.net.wire (.inl ⟨edge.lam,edge.lamBind⟩)) ∧
      tail.head?=some edge.argEnd ∧
      BetaDetourBlocks actualBetaSite.net tail seam (a.cons .empty) remaining := by
  obtain ⟨edge,old,count,relation,stream,positive⟩ := actual_stream a
  obtain ⟨selected,pre,tail,seam,remaining,countEq,split,labels,finish,start,rest⟩ :=
    stream.first_backward actualBetaSite.net positive
  exact ⟨selected,pre,tail,seam,remaining,labels,finish,start,rest⟩

/-- The nine-segment actual reduced path now consumes the general coherent
ancestor theorem. Source I/Transparency come from the real initial encoding
through its boundary-fixed named isomorphism, not fixture hypotheses. -/
theorem actual_coherent_ancestor (a : Context) :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net)),
      SiteBetaGeometry actualBetaSite edge ∧
      BetaPathResidual actualBetaSite edge (reduced.map (plugEnd _ _).invFun) old ∧
      CoherentExpandedCore actualBetaSite.net (.inl ()) old a (a.cons .empty) ∧
      old.head?=some (.inr (.inl (.inl ()))) ∧
      old.getLast?=some (actualBetaSite.outsideEnd lastOutside) := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have invariants := betaEncodingIso.ordinaryInvariants (encode_closed_ordinary_invariants identityApp closed 0)
  exact actualBetaSite.beta_root_coherent_ancestor actualFlow (.inl ()) rfl
    invariants.independence invariants.transparency (reduced_labels a) rfl lastOutside rfl

example : reduced.length=9 := rfl
example : actualBetaSite.net.wire (actualBetaSite.outsideEnd lastOutside) =
    .inl ⟨.inl (.inr (.inl ())),(.inl ())⟩ := rfl
example : (Context.empty.cons (.star .empty)) ≠ (Context.empty.cons (.star .empty)).cons .empty := by
  intro same
  have impossible := congrArg (fun c : Context => c.get 0) same
  cases impossible

#print axioms WireExcursions.beta_entries_forward
#print axioms WireExcursions.beta_lift
#print axioms PathSite.beta_root_ancestor
#print axioms actual_ancestor
#print axioms PathSite.beta_root_forward_ancestor
#print axioms actual_forward_ancestor
#print axioms Labelling.root_forward_of_flow
#print axioms actual_stream
#print axioms actual_first_backward
#print axioms actual_coherent_ancestor

end Lamping.Checks.SoundnessBetaAncestor

namespace Lamping.Checks.SoundnessDetourCoherence
open AG Graph Lambda SoundnessInitialInsertion

theorem nonzero_stream : BetaDetourBlocks (encode 3 identityApp).net
    (inserted 3) (input 3) (output 3) 1 := by
  have body := (bodyLabels 3).ordinary_of_forward _ (bodyForward 3)
  have tailLabels : Labelling (encode 3 identityApp).net ((edge 3).argEnd::suffix 3) (output 3) (output 3) :=
    .cons (.transparent (argumentW 3) false (output 3)) (.single _ _)
  have finish : (pre 3++(edge 3).principal++loopEdges 3).getLast?=
      some ((encode 3 identityApp).net.wire (.inl ⟨(edge 3).lam,(edge 3).lamBind⟩)) := by
    simp only [List.getLast?_append,(actualLoop 3).finish,Option.some_or]
    rfl
  have stream := BetaDetourBlocks.append_backward (encode 3 identityApp).net (edge 3)
    body finish rfl (tailLabels.detour_blocks _)
  simpa only [List.append_assoc,List.singleton_append] using stream

/-- This uses the general decreasing-block theorem, rather than the earlier
fixture-specific manual Core.insert. The real nonzero shell is retained. -/
theorem nonzero_coherent_by_blocks : CoherentExpandedCore (encode 3 identityApp).net (.inl ())
    (inserted 3) (input 3) (output 3) := by
  obtain ⟨flow⟩ := encode_flowBalance identityApp 3
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have invariants := encode_closed_ordinary_invariants identityApp closed 3
  exact nonzero_stream.coherent flow rfl invariants.independence invariants.transparency rfl

example : ExpandedProperPath (encode 3 identityApp).net (.inl ()) (inserted 3) :=
  nonzero_coherent_by_blocks.erase _
example : ExpandedLabelling (encode 3 identityApp).net (inserted 3) (input 3) (output 3) :=
  nonzero_coherent_by_blocks.labelling _

#print axioms BetaDetourBlocks.coherent
#print axioms PathSite.beta_root_coherent_ancestor
#print axioms nonzero_stream
#print axioms nonzero_coherent_by_blocks
end Lamping.Checks.SoundnessDetourCoherence

namespace Lamping.Checks.SoundnessMarkerExpressions
open AG AG.Marker

-- Empty and constant-marker inputs both hide a permutation of old positions.
example : LevelExpr.eval (fun _ => .empty) (.var 0) = LevelExpr.eval (fun _ => .empty) (.var 1) := rfl
example : LevelExpr.eval (fun _ => .star .empty) (.var 0) = LevelExpr.eval (fun _ => .star .empty) (.var 1) := rfl
example : (LevelExpr.var 0) ≠ .var 1 := by decide

-- The height side condition is essential: a short variable code aliases a
-- literal newly written expression, so it cannot be used as a generic marker.
example : LevelExpr.eval (LevelExpr.valuation 1) (.var 0) =
    LevelExpr.eval (LevelExpr.valuation 1) (.o (.star .empty)) := rfl
example : (LevelExpr.var 0) ≠ .o (.star .empty) := by decide
example : ¬(LevelExpr.o (.star .empty)).height<1 := by decide

theorem distinct_variables_real_input :
    LevelExpr.eval (LevelExpr.codeContext 3 2).get (.var 0) ≠
      LevelExpr.eval (LevelExpr.codeContext 3 2).get (.var 1) := by
  intro equal
  have impossible := LevelExpr.finite_codes_injective (gap:=3) (bound:=2)
    (a:=.var 0) (b:=.var 1) (by decide) (by decide) (by decide) (by decide) equal
  cases impossible

theorem no_permutation_cover : ¬∀ input : Context,
    LevelExpr.eval input.get (.var 0)=LevelExpr.eval input.get (.var 1) := by
  intro cover
  exact distinct_variables_real_input (cover (LevelExpr.codeContext 3 2))

example {input : Context} : (LevelExpr.pair (.var 0) (.o (.var 1))).eval input.get =
    .pair (input.get 0) (.o (input.get 1)) := rfl

#print axioms LevelExpr.eval_codes_injective
#print axioms LevelExpr.finite_codes_injective
#print axioms LevelExpr.uniform_system_candidate
#print axioms distinct_variables_real_input
#print axioms no_permutation_cover
end Lamping.Checks.SoundnessMarkerExpressions

namespace Lamping.Checks.SoundnessExpressionPaths
open AG AG.Marker Graph Lambda SoundnessInitialInsertion

theorem no_total_inverse_cro (index : Nat) : ¬∀ input : Context,
    ∃ output, Traversal index (.op .cro) (.inl ()) (.inr ()) input output := by
  intro total
  have symbolicTotal : ∀ input : Context, ∃ output,
      Traversal index (.op .cro) (.inl ()) (.inr ()) (ExprContext.initial.eval input) output := by
    simpa only [ExprContext.eval_initial] using total
  have impossible := expression_input_shape index (.op .cro) (.inl ()) (.inr ()) ExprContext.initial symbolicTotal
  change LevelExpr.var index=LevelExpr.empty at impossible
  cases impossible

/-- The real level3 root-to-binding body path gets all-input existence from
ordinary Independence at its actual typed lambda-binding endpoint. This then
consumes the general expression-trace extraction, not a symbolic-path oracle. -/
theorem nonzero_body_symbolic : ∃ expressions : List ExprContext,
    expressions.head?=some ExprContext.initial ∧
    ∀ input : Context, ContextTrace (encode 3 identityApp).net
      (pre 3++(edge 3).principal++loopEdges 3) (expressions.map (fun c => c.eval input)) := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have independence := encode_closed_independence identityApp closed 3
  have body := (bodyLabels 3).ordinary_of_forward _ (bodyForward 3)
  have finish : (pre 3++(edge 3).principal++loopEdges 3).getLast?=
      some ((encode 3 identityApp).net.wire (.inl ⟨(edge 3).lam,(edge 3).lamBind⟩)) := by
    simp only [List.getLast?_append,(actualLoop 3).finish,Option.some_or]
    rfl
  obtain ⟨allInputs,_⟩ := independence (pre 3++(edge 3).principal++loopEdges 3)
    (.inr (.inl (.inl ()))) (.inl ⟨(edge 3).lam,(edge 3).lamBind⟩)
    .root .lamBind 0 (edge 3).index (input 3) (output 3) rfl finish (.root) trivial
    (.lamBind (edge 3).lam (edge 3).lamBind (edge 3).index (edge 3).lamLabel (edge 3).lamBind_role)
    trivial (bodyForward 3) body
  apply Labelling.expression_trace _ ExprContext.initial
  intro context
  obtain ⟨result,labels⟩ := allInputs context
  exact ⟨result,by simpa only [Context.replace_zero,ExprContext.eval_initial] using labels⟩

#print axioms expression_input_shape
#print axioms total_expression_output
#print axioms Labelling.expression_trace
#print axioms no_total_inverse_cro
#print axioms nonzero_body_symbolic
end Lamping.Checks.SoundnessExpressionPaths

namespace Lamping.Checks.SoundnessUniformBinder
open AG AG.Marker Graph Lambda SoundnessInitialInsertion

/-- The original level3 Star shell belongs to this actual lambda-context
occurrence. The theorem keeps that physical occurrence for every other
actual full/prefix assignment, rather than picking a new binder witness. -/
theorem nonzero_binder_stable (newInput newMiddle newOutput : Context)
    (labels : Labelling (encode 3 identityApp).net
      (pre 3++(edge 3).principal++loopEdges 3) newInput newOutput)
    (prefixLabels : Labelling (encode 3 identityApp).net
      (pre 3++(edge 3).principal) newInput newMiddle) :
    Context.SameShell 3 newMiddle newOutput := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have invariants := encode_closed_ordinary_invariants identityApp closed 3
  have originalPrefix : Labelling (encode 3 identityApp).net
      (pre 3++(edge 3).principal) (input 3) (input 3) :=
    .cons ((edge 3).app_fun_turn (input 3))
      (.cons (LabelledTurn.transparent (g:=(encode 3 identityApp).net) (.inr (.inl (.inl ()))) false (input 3)) (.single _ _))
  have finish : (pre 3++(edge 3).principal++loopEdges 3).getLast?=
      some ((encode 3 identityApp).net.wire (.inl ⟨(edge 3).lam,(edge 3).lamBind⟩)) := by
    simp only [List.getLast?_append,(actualLoop 3).finish,Option.some_or]
    rfl
  exact binder_shell_stable invariants.independence invariants.nesting invariants.transparency
    (edge 3) _ (pre 3++(edge 3).principal) (loopEdges 3) (input 3) (input 3) (output 3)
    rfl (bodyForward 3) finish ((bodyLabels 3).ordinary_of_forward _ (bodyForward 3))
    rfl originalPrefix rfl actual_shell newInput newMiddle newOutput labels prefixLabels

#print axioms LevelExpr.uniform_system_candidate_finite
#print axioms uniform_shell_ordinal
#print axioms binder_shell_stable
#print axioms nonzero_binder_stable
end Lamping.Checks.SoundnessUniformBinder

namespace Lamping.Checks.SoundnessTypedDetours
open AG Graph Lambda SoundnessInitialInsertion

/-- Every requested root context gets a genuinely rebuilt coherent derivation
on the SAME eleven physical segments of the nonzero-level fixture. -/
theorem nonzero_all_inputs (requested : Context) : ∃ result,
    CoherentExpandedCore (encode 3 identityApp).net (.inl ()) (inserted 3) requested result := by
  obtain ⟨flow⟩ := encode_flowBalance identityApp 3
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have invariants := encode_closed_ordinary_invariants identityApp closed 3
  exact SoundnessDetourCoherence.nonzero_stream.typed_root_inputs flow rfl invariants rfl
    (.inl ⟨.inr (.inr (.inl ())),.inl ()⟩) .lamCtx 4 rfl
    (.lamCtx _ _ 4 rfl HEq.rfl) trivial requested

/-- The reverse-route cut inherits labels from the supplied actual eleven
segment typed extension, for every input. This is not arbitrary completion. -/
theorem nonzero_cut_all_inputs (requested : Context) :
    CoherentExpandedPrefix (encode 3 identityApp).net (.inl ()) ((inserted 3).take 8) requested := by
  obtain ⟨flow⟩ := encode_flowBalance identityApp 3
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have invariants := encode_closed_ordinary_invariants identityApp closed 3
  have path : BetaDetourBlocks (encode 3 identityApp).net ((inserted 3).take 8++(inserted 3).drop 8)
      (input 3) (output 3) 1 := by
    rw [List.take_append_drop]; exact SoundnessDetourCoherence.nonzero_stream
  exact path.typed_prefix_inputs flow rfl invariants
    (by rw [List.take_append_drop]; rfl)
    (.inl ⟨.inr (.inr (.inl ())),.inl ()⟩) .lamCtx 4
    (by rw [List.take_append_drop]; rfl) (.lamCtx _ _ 4 rfl HEq.rfl) trivial
    (by intro empty; have impossible := congrArg List.length empty; change 8=0 at impossible; omega) requested

/-- Choose the actual ancestor once at the empty assignment, then rebuild
coherent labels on that fixed physical ancestor for EVERY requested input. -/
theorem actual_fixed_ancestor_all_inputs :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net)),
      BetaPathResidual actualBetaSite edge
        (SoundnessBetaAncestor.reduced.map (plugEnd _ _).invFun) old ∧
      ∀ requested : Context, ∃ result,
        CoherentExpandedCore actualBetaSite.net (.inl ()) old requested result := by
  obtain ⟨edge,old,geometry,relation,labels,first,last⟩ := SoundnessBetaAncestor.actual_ancestor Context.empty
  obtain ⟨count,stream⟩ := relation.detour_blocks actualBetaSite geometry
    ((SoundnessBetaAncestor.reduced_labels Context.empty).plug_decomposition _ _)
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have invariants := betaEncodingIso.ordinaryInvariants (encode_closed_ordinary_invariants identityApp closed 0)
  refine ⟨edge,old,relation,?_⟩
  exact stream.typed_root_inputs SoundnessBetaAncestor.actualFlow rfl invariants first
    (.inl ⟨.inl (.inr (.inl ())),.inl ()⟩) .lamCtx 1 last
    (.lamCtx _ _ 1 rfl HEq.rfl) trivial

#print axioms BetaDetourBlocks.typed_root_inputs
#print axioms nonzero_all_inputs
#print axioms BetaDetourBlocks.typed_prefix_inputs
#print axioms nonzero_cut_all_inputs
#print axioms actual_fixed_ancestor_all_inputs
end Lamping.Checks.SoundnessTypedDetours

namespace Lamping.Checks.SoundnessBetaContraction
open AG Graph Lambda SoundnessBetaAncestor

/-- The skeleton's assignment is empty, while the contracted ancestor has
the caller's arbitrary input and a genuinely changed output. -/
theorem actual_contract (requested : Context) :
    Labelling actualBetaSite.reduce reduced requested (requested.cons .empty) := by
  obtain ⟨edge,old,geometry,relation,coherent,_,_⟩ := actual_coherent_ancestor requested
  exact relation.contract_actual actualBetaSite geometry (reduced_labels Context.empty) (coherent.labelling _)

/-- This consumes the new beta-step root-existence theorem, then separately
identifies its output with the independently constructed fixture labels. -/
theorem actual_rebuilt_labels (requested : Context) :
    Labelling actualBetaSite.reduce reduced requested (requested.cons .empty) := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have invariants := betaEncodingIso.ordinaryInvariants (encode_closed_ordinary_invariants identityApp closed 0)
  obtain ⟨result,labels⟩ := actualBetaSite.beta_typed_root_inputs actualFlow (.inl ()) rfl invariants
    (reduced_labels Context.empty) rfl (.inl ⟨.inl (.inr (.inl ())),.inl ()⟩) .lamCtx 1 rfl
    (.lamCtx _ _ 1 rfl HEq.rfl) trivial requested
  have same := labels.output_unique (reduced_labels requested)
  rw [same] at labels
  exact labels

example : Labelling actualBetaSite.reduce reduced (Context.empty.cons (.star .empty))
    ((Context.empty.cons (.star .empty)).cons .empty) := actual_rebuilt_labels _

#print axioms ExpandedTurn.ordinary_of_shape
#print axioms BetaPathResidual.contract
#print axioms BetaPathResidual.contract_actual
#print axioms PathSite.beta_root_inputs
#print axioms PathSite.beta_outside_incoming
#print axioms PathSite.beta_typed_root_inputs
#print axioms actual_contract
#print axioms actual_rebuilt_labels
end Lamping.Checks.SoundnessBetaContraction

namespace Lamping.Checks.SoundnessHighTails
open AG Graph Lambda SoundnessInitialInsertion

theorem appArg_same_width_no_sync : ¬∀ replacement : Context,
    Traversal 0 (.op .app) AG.appCtx AG.appArg replacement (Context.empty.replace 1 replacement) := by
  intro synchronize
  have same := (synchronize (Context.empty.cons (.star .empty))).proper_context
  have impossible := congrArg (fun c : Context => c.get 0) same
  cases impossible

theorem actual_appArg_loss : ∃ loss : Nat,0<loss ∧
    ∀ replacement,Traversal 0 (.op .app) AG.appCtx AG.appArg
      (Context.empty.replace loss replacement) (Context.empty.replace 1 replacement) := by
  obtain ⟨loss,_,sync⟩ := (Traversal.direct (Passage.appArg (i:=0) Context.empty)).high_tail_sync
    0 0 1 trivial rfl rfl ⟨rfl,Or.inr rfl⟩ 0
  refine ⟨loss,?_,?_⟩
  · apply Classical.byContradiction
    intro notPositive
    have zero : loss=0 := by omega
    subst loss
    exact appArg_same_width_no_sync (by simpa using sync)
  · simpa only [Nat.zero_add,Nat.add_zero] using sync

theorem actual_bra_strict_sync : ∃ loss : Nat,
    ∀ replacement,Traversal 0 (.op .bra) (.inr ()) (.inl ())
      ((((Context.empty.cons (.star .empty)).cons .empty)).replace (2+loss) replacement)
      ((Context.empty.cons (.pair (.star .empty) .empty)).replace 1 replacement) := by
  obtain ⟨loss,_,sync⟩ := bra_equal_height_actual.high_tail_sync 1 2 1 (by change (0 : Int)<1; decide) rfl rfl trivial 0
  exact ⟨loss,by simpa only [Nat.add_zero] using sync⟩

/-- The actual encoded app-argument prefix has unchanged Context and geometric
height 3→4. Its synchronous source width must therefore grow strictly. -/
theorem nonzero_argument_prefix_sync : ∃ width,3<width ∧
    ∀ replacement,Labelling (encode 3 identityApp).net (pre 3++[(edge 3).argEnd])
      ((input 3).replace width replacement) ((input 3).replace 4 replacement) := by
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 3
  have labels : Labelling (encode 3 identityApp).net (pre 3++[(edge 3).argEnd]) (input 3) (input 3) :=
    .cons ((edge 3).app_arg_turn (input 3)) (.single _ _)
  have forward : Forward (encode 3 identityApp).net (pre 3++[(edge 3).argEnd]) :=
    .node (.inl (.inl ())) AG.appCtx AG.appArg rfl rfl ⟨rfl,Or.inr rfl⟩ (.single _)
  obtain ⟨width,lower,tailEq,sync⟩ := labels.high_tail_sync balance forward 3 4
    (by intro e head; cases Option.some.inj head; rfl)
    (by intro e finish; cases Option.some.inj finish; rfl)
  have notThree : width≠3 := by
    intro same
    subst width
    have impossible := congrArg (fun c : Context => c.get 0) tailEq
    cases impossible
  exact ⟨width,by omega,sync⟩

theorem actual_argument_independence_tail (a : Context) : ∃ width,0<width ∧
    ∀ replacement,Labelling (encode 0 identityApp).net ((edge 0).argEnd::suffix 0)
      (a.replace width replacement) (a.replace 1 replacement) := by
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  have labels : Labelling (encode 0 identityApp).net ((edge 0).argEnd::suffix 0) a a :=
    .cons (LabelledTurn.transparent (g:=(encode 0 identityApp).net) (argumentW 0) false a) (.single _ _)
  obtain ⟨width,_,strict,_,sync⟩ := balance.independence_tail (.inl ()) rfl _ (edge 0).argEnd
    (.inl ⟨.inr (.inr (.inl ())),.inl ()⟩) .appArg .lamCtx 0 1 a a rfl rfl
    (.appArg (edge 0).app (edge 0).appArg 0 rfl HEq.rfl) trivial
    (.lamCtx _ _ 1 rfl HEq.rfl) trivial
    (.transparent (argumentW 0) false rfl rfl (.single _)) labels
  exact ⟨width,strict rfl,sync⟩

#print axioms bra_equal_height_actual
#print axioms bra_equal_height_no_sync
#print axioms Traversal.high_tail_sync
#print axioms Labelling.high_tail_sync
#print axioms IndexedLevelBalance.independence_tail
#print axioms appArg_same_width_no_sync
#print axioms actual_appArg_loss
#print axioms actual_bra_strict_sync
#print axioms nonzero_argument_prefix_sync
#print axioms actual_argument_independence_tail
end Lamping.Checks.SoundnessHighTails

namespace Lamping.Checks.SoundnessMatchingChildren
open AG Graph Lambda SoundnessInitialInsertion

def parentAccess : RootAccess (encode 3 identityApp).net (.inl ()) :=
  ⟨pre 3,⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.app,rfl⟩⟩⟩

def functionAccess : RootAccess (encode 3 identityApp).net (.inl ()) :=
  ⟨pre 3++(edge 3).principal,⟨⟨⟨Context.empty,Context.empty,
    .cons ((edge 3).app_fun_turn Context.empty)
      (.cons (LabelledTurn.transparent (g:=(encode 3 identityApp).net)
        (.inr (.inl (.inl ()))) false Context.empty) (.single _ _))⟩,
    .node (.inl (.inl ())) AG.appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩
      (.transparent (.inr (.inl (.inl ()))) false rfl rfl (.single _))⟩,
    rfl,⟨.lam,rfl⟩⟩⟩

/-- The general Matches theorem constructs the child; its word bijection
then identifies it with this independent literal three-segment access. -/
theorem actual_function_child : ∃ (child : RootAccess (encode 3 identityApp).net (.inl ()))
    (tail : List (Endpoint (encode 3 identityApp).net)),
    child.val=parentAccess.val++(edge 3).funEnd::tail ∧
    child=functionAccess ∧accessWord (encode 3 identityApp).net child.val=[.fn] := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching := encode_closed_matches identityApp closed 3
  obtain ⟨child,tail,split,word⟩ := matching.function_child_access parentAccess (edge 3).app
    (edge 3).appCtx (edge 3).appFun 3 rfl HEq.rfl HEq.rfl rfl
  have actualWord : accessWord (encode 3 identityApp).net child.val=[.fn] := word
  have same : child=functionAccess := matching.accessWord_injective (by exact actualWord)
  exact ⟨child,tail,split,same,actualWord⟩

theorem actual_function_suffix_input (requested : Context) :
    ∃ (child : RootAccess (encode 3 identityApp).net (.inl ()))
      (tail : List (Endpoint (encode 3 identityApp).net)),
      child=functionAccess ∧child.val=parentAccess.val++(edge 3).funEnd::tail ∧
      Labelling (encode 3 identityApp).net ((edge 3).funEnd::tail) requested requested := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching := encode_closed_matches identityApp closed 3
  have indep := encode_closed_independence identityApp closed 3
  obtain ⟨child,tail,split,word,_,inputs⟩ := matching.function_child_input indep parentAccess
    (edge 3).app (edge 3).appCtx (edge 3).appFun 3 rfl HEq.rfl HEq.rfl rfl
  have same : child=functionAccess := matching.accessWord_injective (by exact word)
  obtain ⟨output,full,suffixLabels⟩ := inputs requested requested (.single _ _)
  have literal : Labelling (encode 3 identityApp).net functionAccess.val requested requested :=
    .cons ((edge 3).app_fun_turn requested)
      (.cons (LabelledTurn.transparent (g:=(encode 3 identityApp).net)
        (.inr (.inl (.inl ()))) false requested) (.single _ _))
  rw [←same] at literal
  have outputEq := full.output_unique literal
  rw [outputEq] at suffixLabels
  exact ⟨child,tail,same,split,suffixLabels⟩

/-- A genuine direct principal edge reaches the lambda immediately, so the
function-token reflection must allow an empty remaining tail. -/
def directFunctionAccess : RootAccess SoundnessPrefix.net () :=
  ⟨[.inr (.inl ()),.inl ⟨.app,.inl ()⟩],
    ⟨⟨⟨Context.empty,Context.empty,
      .cons (SoundnessPrefix.edge.app_fun_turn Context.empty) (.single _ _)⟩,
      .node .app AG.appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ (.single _)⟩,
      rfl,⟨.lam,rfl⟩⟩⟩

theorem direct_child_empty_tail : ∃ (parent : RootAccess SoundnessPrefix.net ())
    (node : SoundnessPrefix.Node) (ctx funPort : Port (SoundnessPrefix.net.label node).sort)
    (tail : List (Endpoint SoundnessPrefix.net)),
    directFunctionAccess.val=parent.val++(.inl ⟨node,funPort⟩)::tail ∧
    tail=[] ∧parent.val=[.inr (.inl ())] ∧
    parent.val.getLast?=some (SoundnessPrefix.net.wire (.inl ⟨node,ctx⟩)) := by
  obtain ⟨parent,node,ctx,funPort,tail,_,_,_,_,_,finish,split⟩ :=
    directFunctionAccess.before_function_token [] rfl
  have parentPositive : 0<parent.val.length := List.length_pos_iff.mpr (by
    intro empty; have first := parent.property.2.1; rw [empty] at first; cases first)
  have sizes := congrArg List.length split
  rw [List.length_append,List.length_cons] at sizes
  change 2=parent.val.length+(tail.length+1) at sizes
  have tailEmpty : tail=[] := List.length_eq_zero_iff.mp (by omega)
  have parentLength : parent.val.length=1 := by omega
  obtain ⟨rest,parentSplit⟩ := List.head?_eq_some_iff.mp parent.property.2.1
  have restLength : rest.length+1=1 := by simpa only [parentSplit,List.length_cons] using parentLength
  have restEmpty : rest=[] := List.length_eq_zero_iff.mp (by omega)
  exact ⟨parent,node,ctx,funPort,tail,split,tailEmpty,by rw [parentSplit,restEmpty],finish⟩

#print axioms Matches.accessWord_injective
#print axioms RootAccess.before_function_token
#print axioms Matches.function_child_access
#print axioms actual_function_child
#print axioms direct_child_empty_tail
#print axioms RootAccess.incoming_endpoint
#print axioms RootAccess.inputs
#print axioms Matches.function_child_input
#print axioms Traversal.control_auxiliary_unique
#print axioms PathSite.matched_control_inputs
#print axioms PathSite.matched_control_input
#print axioms PathSite.matched_control_input_of_prefix
#print axioms actual_function_suffix_input
end Lamping.Checks.SoundnessMatchingChildren









namespace Lamping.Checks.SoundnessControlTransfer
open Lamping.AG Lamping.Graph

def oldO : Context := Context.empty.cons (.o .empty)
def highChanged : Context := (Context.empty.cons (.star .empty)).cons (.o .empty)

theorem old_inverse : Traversal 0 (.op .fan) (.inl ()) fanO oldO Context.empty := by
  simpa [oldO] using Traversal.inverse (Passage.fanO (i:=0) Context.empty Context.empty .empty)

theorem changed_high_inverse : ∃ result,Traversal 0 (.op .fan) (.inl ()) fanO highChanged result :=
  old_inverse.control_inverse_transfer (Or.inl rfl) highChanged rfl

theorem high_really_changed : highChanged.get 1≠oldO.get 1 := by
  intro equal
  cases equal

theorem wrong_constructor_no_inverse : ¬∃ result,Traversal 0 (.op .fan) (.inl ()) fanO Context.empty result := by
  rintro ⟨result,rule⟩
  have marker := rule.fan_marker
  simp [FanEdgeMarker,AG.fanO] at marker

#print axioms Traversal.control_inverse_transfer
#print axioms changed_high_inverse
#print axioms high_really_changed
#print axioms wrong_constructor_no_inverse
#print axioms Marker.binder_shell_stable_node
#print axioms PathSite.binding_control_input_stable
#print axioms PathSite.action_canonical_ancestor
#print axioms PathSite.action_root_relabelling_ancestor
#print axioms PathSite.fan_new_lam_bind_root_inputs
#print axioms PathSite.cro_new_lam_bind_root_inputs
#print axioms PathSite.bra_new_lam_bind_root_inputs
#print axioms PathSite.action_typed_root_inputs
end Lamping.Checks.SoundnessControlTransfer

namespace Lamping.Checks.SoundnessBetaBindingTransport
open AG Graph Lambda
abbrev source := actualBetaSite.net
abbrev cut := cutFragment source (pathPartition (Schema.beta 0) Unit) actualBetaSite.closed
abbrev rhs := wires Bool Bool boolFlip
abbrev retainedLambda : BetaKept := .inr (.inl ())
abbrev retainedCro : BetaKept := .inr (.inr ())
def argBody : BetaW := .inl (.inr (.inr (.inl ())))
def argBind : BetaW := .inl (.inr (.inr (.inr ⟨0,rfl⟩)))
def cutLoop : List (Endpoint cut) :=
  [.inl ⟨retainedLambda,lamBody⟩,.inr (.inr (argBody,true)),
   .inl ⟨retainedCro,.inl ()⟩,.inr (.inr (argBind,false))]
theorem cut_labels (a : Context) : Labelling cut cutLoop a (InitialOffsets.croAt 1 a) := by
  apply Labelling.cons (LabelledTurn.transparent (g:=cut) argBody false a)
  apply Labelling.cons (LabelledTurn.node (g:=cut) retainedCro (.inr ()) (.inl ())
    (.direct (InitialOffsets.Event.apply_rel (.cro 1) a)))
  exact .cons (LabelledTurn.transparent (g:=cut) argBind true _) (.single _ _)

private theorem raw_left {es : List (Endpoint cut)} {a b : Context} (labels : Labelling cut es a b) :
    PlugLabelling cut rhs (es.map Sum.inl) a b := by
  induction labels with
  | single e a => exact .single _ _
  | cons turn tail ih => exact .cons (.left turn) ih

private theorem source_left {es : List (Endpoint cut)} {a b : Context} (labels : Labelling cut es a b) :
    Labelling source (es.map actualBetaSite.outsideEnd) a b := by
  induction labels with
  | single e a => exact .single _ _
  | cons turn tail ih =>
    apply Labelling.cons
    · rw [actualBetaSite.outsideEnd_wire]
      exact turn.outsideEnd actualBetaSite
    · exact ih

def oldLoop := cutLoop.map actualBetaSite.outsideEnd

def binding (a : Context) : BindingLoop source oldLoop a (InitialOffsets.croAt 1 a) where
  binder := .inl retainedLambda
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := source_left (cut_labels a)
  forward := by
    apply (source_left (cut_labels a)).forward_of_flow SoundnessBetaAncestor.actualFlow
    intro e head
    have same : e=(.inl ⟨.inl retainedLambda,lamBody⟩ : Endpoint source) := (Option.some.inj head).symm
    subst e
    rfl
  shell := by
    intro k low
    have zero : k=0 := by change k<1 at low; omega
    subst k
    rfl

theorem residual (edge : BetaEdge source) :
    BetaPathResidual actualBetaSite edge (cutLoop.map Sum.inl) oldLoop :=
  .outside (.outside (.outside (.single _)))

theorem actual_kept_loop_transport (a : Context) :
    ∃ loop : BindingLoop actualBetaSite.reduce ((cutLoop.map Sum.inl).map (plugEnd cut.label rhs.label))
      a (InitialOffsets.croAt 1 a),loop.binder=.inl retainedLambda := by
  obtain ⟨edge,geometry⟩ := actualBetaSite.siteBetaGeometry_exists
  have shape := raw_left (cut_labels a)
  obtain ⟨reducedFlow⟩ := actualBetaSite.reduce_flowBalance SoundnessBetaAncestor.actualFlow
  have forward := (shape.actual cut rhs).forward_of_flow reducedFlow (by
    intro e head
    have same : e=(.inl ⟨.inl retainedLambda,lamBody⟩ : Endpoint actualBetaSite.reduce) := (Option.some.inj head).symm
    subst e
    rfl)
  exact (residual edge).contract_kept_binding_loop actualBetaSite geometry shape forward
    (binding a).expanded retainedLambda rfl

theorem preserved_low_star : (InitialOffsets.croAt 1 (Context.empty.cons (.star .empty))).get 0=.star .empty := rfl

theorem actual_selected_ordinal (edge : BetaEdge source) (geometry : SiteBetaGeometry actualBetaSite edge) :
    ∃ cutAt : BetaResidualOccurrence actualBetaSite edge (cutLoop.map Sum.inl) oldLoop
        (.inl ⟨retainedCro,.inl ()⟩) 2,
      cutAt.oldBefore=oldLoop.take 2 ∧cutAt.oldAfter=oldLoop.drop 3 := by
  exact (residual edge).split_kept_departure actualBetaSite geometry retainedCro (.inl ())
    (oldLoop.take 2) (oldLoop.drop 3) rfl

/-- The exclusion genuinely needs retained endpoints: the active application
departure really occurs on this actual beta principal route. -/
theorem active_principal_not_excluded : ∃ edge : BetaEdge source,
    SiteBetaGeometry actualBetaSite edge ∧edge.funEnd∈edge.principal := by
  obtain ⟨edge,geometry⟩ := actualBetaSite.siteBetaGeometry_exists
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp edge.principalStart
  exact ⟨edge,geometry,by rw [split]; exact List.mem_cons_self⟩

#print axioms actual_kept_loop_transport
#print axioms preserved_low_star
#print axioms actual_selected_ordinal
#print axioms active_principal_not_excluded
#print axioms BetaPathResidual.split_occurrence
#print axioms BetaPathResidual.contract_binding_prefix_actual
end Lamping.Checks.SoundnessBetaBindingTransport

namespace Lamping.Checks.SoundnessBetaShellReflection
open AG Graph Lambda SoundnessBetaBindingTransport

theorem actual_loop_shell_reflection (a changed : Context)
    (sameOutput : Context.SameShell 2 (InitialOffsets.croAt 1 a) (InitialOffsets.croAt 1 changed)) :
    Context.SameShell 1 a changed := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have indep := (betaEncodingIso.ordinaryInvariants (encode_closed_ordinary_invariants identityApp closed 0)).independence
  exact indep.reflect_shell oldLoop (.inl ⟨.inl retainedLambda,lamBody⟩) (.inl ⟨.inl retainedLambda,lamBind⟩)
    .lamBody .lamBind 1 1 a (InitialOffsets.croAt 1 a) changed (InitialOffsets.croAt 1 changed)
    rfl rfl (AtProperRole.lamBody (g:=source) (root:=.inl ()) (.inl retainedLambda) lamBody 1 rfl HEq.rfl) trivial
    (AtProperRole.lamBind (g:=source) (root:=.inl ()) (.inl retainedLambda) lamBind 1 rfl HEq.rfl) trivial
    (binding a).forward (binding a).proper (binding changed).proper sameOutput

theorem zero_shell_does_not_reflect :
    Context.SameShell 0 (InitialOffsets.croAt 1 Context.empty)
      (InitialOffsets.croAt 1 (Context.empty.cons (.star .empty))) ∧
      ¬Context.SameShell 1 Context.empty (Context.empty.cons (.star .empty)) := by
  constructor
  · intro k low; omega
  · intro shell
    have bad := shell 0 (by decide)
    cases bad

#print axioms actual_loop_shell_reflection
#print axioms zero_shell_does_not_reflect
#print axioms Independence.reflect_shell
#print axioms IndexedLevelBalance.reflect_shell
#print axioms Independence.reflect_lambda_prefix
end Lamping.Checks.SoundnessBetaShellReflection

namespace Lamping.Checks.SoundnessBetaTransparency
open AG Graph Lambda
open SoundnessBetaAncestor SoundnessBetaBindingTransport

abbrev targetLoop : List (Endpoint actualBetaSite.reduce) :=
  ((cutLoop.map Sum.inl).map (plugEnd SoundnessBetaBindingTransport.cut.label rhs.label))
def bindingPath := reduced++targetLoop
abbrev finalContext (a : Context) := InitialOffsets.croAt 1 (a.cons .empty)

private theorem left_labels {es : List (Endpoint SoundnessBetaBindingTransport.cut)} {a b : Context}
    (labels : Labelling SoundnessBetaBindingTransport.cut es a b) :
    PlugLabelling SoundnessBetaBindingTransport.cut rhs (es.map Sum.inl) a b := by
  induction labels with
  | single e a => exact .single _ _
  | cons turn tail ih => exact .cons (.left turn) ih

theorem target_loop_labels (a : Context) :
    Labelling actualBetaSite.reduce targetLoop a (InitialOffsets.croAt 1 a) :=
  (left_labels (cut_labels a)).actual _ _

/-- This literal thirteen-segment reduced path crosses BOTH beta wires,
then continues through the retained lambda body and its Cro1 to binding.
Its lifted stream therefore has a genuinely nonzero backward-block count. -/
theorem binding_path_labels (a : Context) :
    Labelling actualBetaSite.reduce bindingPath a (finalContext a) := by
  apply (reduced_labels a).append_seam (target_loop_labels (a.cons .empty))
  intro e f atE atF
  have sameE : e=actualBetaSite.reduce.wire (.inl ⟨.inl retainedLambda,(.inl ())⟩) := by
    exact Option.some.inj atE.symm
  have sameF : f=(.inl ⟨.inl retainedLambda,lamBody⟩ : Endpoint actualBetaSite.reduce) := by
    exact (Option.some.inj atF).symm
  rw [sameE,sameF,Pairing.involutive]
  exact LabelledTurn.node (g:=actualBetaSite.reduce) (.inl retainedLambda) (.inl ()) lamBody (.direct (.lamBody _))

theorem actual_reduced_transparency : Transparency actualBetaSite.reduce (.inl ()) := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have initial := betaEncodingIso.ordinaryInvariants (encode_closed_ordinary_invariants identityApp closed 0)
  exact actualBetaSite.beta_transparency actualFlow (.inl ()) rfl initial.independence initial.transparency

theorem actual_binding_transparency (a : Context) :
    ∃ (pre loop : List (Endpoint actualBetaSite.reduce)) (middle : Context)
      (binding : BindingLoop actualBetaSite.reduce loop middle (finalContext a)),
      bindingPath=pre++loop ∧ binding.binder=.inl retainedLambda ∧
      pre.getLast?=some (actualBetaSite.reduce.wire (.inl ⟨.inl retainedLambda,(.inl ())⟩)) ∧
      Labelling actualBetaSite.reduce pre a middle := by
  obtain ⟨newFlow⟩ := actualBetaSite.reduce_flowBalance actualFlow
  have forward := (binding_path_labels a).root_forward_of_flow newFlow (.inl ()) rfl rfl
  exact actual_reduced_transparency bindingPath a (finalContext a) (.inl retainedLambda)
    (.inl ()) lamBody lamBind rfl HEq.rfl HEq.rfl HEq.rfl rfl rfl forward (binding_path_labels a)

abbrev bindingLast : Endpoint SoundnessBetaAncestor.cut :=
  SoundnessBetaAncestor.cut.wire (.inl ⟨retainedLambda,lamBind⟩)

theorem actual_positive_binding_stream (a : Context) :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net)) (count : Nat)
      (pre loop : List (Endpoint actualBetaSite.net)) (middle : Context)
      (binding : ExpandedBindingLoop actualBetaSite.net loop middle (finalContext a)),
      BetaPathResidual actualBetaSite edge (bindingPath.map (plugEnd _ _).invFun) old ∧
      BetaDetourBlocks actualBetaSite.net old a (finalContext a) count ∧ 0<count ∧
      old=pre++loop ∧ binding.binder=.inl retainedLambda ∧
      pre.getLast?=some (actualBetaSite.net.wire (.inl ⟨.inl retainedLambda,(.inl ())⟩)) ∧
      ExpandedLabelling actualBetaSite.net pre a middle := by
  obtain ⟨edge,old,geometry,relation,_labels,first,last⟩ :=
    actualBetaSite.beta_root_ancestor actualFlow (.inl ()) rfl (binding_path_labels a) rfl bindingLast rfl
  obtain ⟨count,stream⟩ := relation.detour_blocks actualBetaSite geometry ((binding_path_labels a).plug_decomposition _ _)
  have entry : (.inr (.inr (.inl (.inr false)))) ∈ bindingPath.map (plugEnd _ _).invFun := by
    exact List.mem_map.mpr ⟨.inr (.inr (.inr (.inr false),true)),by simp [bindingPath,reduced],rfl⟩
  have positive := stream.positive_count actualBetaSite.net actualFlow (.inl ()) rfl first edge
    (relation.reverse_occurs actualBetaSite entry)
  have oldFinish : old.getLast?=some (actualBetaSite.net.wire (.inl ⟨.inl retainedLambda,lamBind⟩)) := by
    rw [←actualBetaSite.outsideEnd_wire] at last
    exact last
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have initial := betaEncodingIso.ordinaryInvariants (encode_closed_ordinary_invariants identityApp closed 0)
  obtain ⟨pre,loop,middle,binding,split,binderEq,preEnd,preLabels⟩ := stream.transparency actualFlow rfl
    initial.independence initial.transparency (.inl retainedLambda) (.inl ()) lamBody lamBind
    rfl HEq.rfl HEq.rfl HEq.rfl first oldFinish
  exact ⟨edge,old,count,pre,loop,middle,binding,relation,stream,positive,split,binderEq,preEnd,preLabels⟩

example : bindingPath.length=13 := rfl
example : (finalContext (Context.empty.cons (.star .empty))).get 1=.empty := rfl
example : (finalContext (Context.empty.cons (.star .empty))).get 2=.star .empty := rfl
example : Context.empty.cons (.star .empty)≠finalContext (Context.empty.cons (.star .empty)) := by
  intro same
  have low := congrArg (fun c : Context => c.get 0) same
  cases low

#print axioms BetaEdge.transparency_splice
#print axioms BetaDetourBlocks.transparency
#print axioms PathSite.beta_transparency
#print axioms binding_path_labels
#print axioms actual_reduced_transparency
#print axioms actual_binding_transparency
#print axioms actual_positive_binding_stream
end Lamping.Checks.SoundnessBetaTransparency

#print axioms Lamping.AG.ActionCanonicalLocal.kept_not_tail
#print axioms Lamping.AG.ActionCanonicalBlocks.split_kept_occurrence
#print axioms Lamping.AG.ActionCanonicalBlocks.split_kept_decomposition
#print axioms Lamping.AG.ActionCanonicalBlocks.source_labels
#print axioms Lamping.AG.Labelling.before_lambda_body
#print axioms Lamping.AG.ActionCanonicalBlocks.kept_binding_prefix
#print axioms Lamping.AG.PathSite.action_kept_transparency

namespace Lamping.Checks.SoundnessCopiedTransparency
open AG Graph
private def kept : Empty → Label signature := Empty.elim
private abbrev schema : Schema := .fanAction .lam 2 3 (by decide)
def site : PathSite schema kept (B:=Bool⊕Bool) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl k,_⟩ => nomatch k
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inl _),.inr a⟩ => .inr (.inl (.inl a))
      | .inl ⟨.inr (.inr _),.inr a⟩ => .inl ⟨.inr (.inr ()),.inr (!a)⟩
      | .inr (.inl (.inl a)) => .inl ⟨.inr (.inl ()),.inr a⟩
      | .inr (.inl (.inr a)) => .inr (.inl (.inr (!a)))
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
      · exact nomatch k
      · cases u; cases p with | inl u => cases u; rfl | inr a => cases a <;> rfl
      · cases u; cases p with | inl u => cases u; rfl | inr a => cases a <;> rfl
      · rfl
      · cases a <;> rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩)) same
      · exact nomatch k
      · cases p with | inl u => cases same | inr a => cases a <;> cases same
      · cases p with | inl u => cases same | inr a => cases a <;> cases same
      · cases same
      · cases a <;> cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

def boundary : Bool⊕Bool → Bool | .inl _ => true | .inr b => b
def flow : FlowBalance site.net boundary where
  nodes := fun _ => true
  vertices := fun | .inl e => nomatch e | .inr _ => false
  wiring := by
    rintro (⟨k|(u|u),p⟩ | ((a|a) | ⟨w|v,d⟩))
    · exact nomatch k
    · cases p with | inl u => cases u; rfl | inr a => cases a <;> rfl
    · cases p with | inl u => cases u; rfl | inr a => cases a <;> rfl
    · rfl
    · cases a <;> rfl
    · exact nomatch w
    · cases d <;> rfl

abbrev sourcePre (branch : Bool) : List (Endpoint site.net) :=
  [.inr (.inl (.inl branch)),.inl ⟨.inr (.inl ()),.inl ()⟩,.inr (.inr (.inr (),true))]
abbrev sourceLoop : List (Endpoint site.net) := [.inl ⟨.inr (.inr ()),lamBody⟩]

theorem source_labels (branch : Bool) (a : Context) :
    Labelling site.net (sourcePre branch++sourceLoop) a (InitialOffsets.fanAt 2 branch a) :=
  .cons (LabelledTurn.node (g:=site.net) (.inr (.inl ())) (.inr branch) (.inl ())
    (.direct (InitialOffsets.Event.apply_rel (.fan 2 branch) a)))
    (.cons (LabelledTurn.transparent (g:=site.net) (.inr ()) false _)
      (.cons (LabelledTurn.node (g:=site.net) (.inr (.inr ())) (.inl ()) lamBody (.direct (.lamBody _))) (.single _ _)))

/-- The source has exactly one rooted forward route to binding: the actual
fan writer, the one W subdivision, then lambda body. Its T is proved from
that finite geometry rather than supplied as a fixture assumption. -/
theorem source_transparency (branch : Bool) : Transparency site.net (.inl branch) := by
  intro es a b node ctx body bind isLam ctxRole bodyRole bindRole rooted finish fw labels
  rcases node with e |(u|u)
  · exact nomatch e
  · cases isLam
  · cases u
    have hc : ctx=.inl () := eq_of_heq ctxRole
    have hb : body=lamBody := eq_of_heq bodyRole
    have hv : bind=lamBind := eq_of_heq bindRole
    subst ctx
    subst body
    subst bind
    obtain ⟨rest,split⟩ := List.head?_eq_some_iff.mp rooted
    subst es
    cases labels with
    | single => cases finish
    | cons first after =>
      cases first with
      | node node p q rule =>
        cases q with
        | inr other => exact False.elim rule.aux_aux
        | inl u =>
          cases u
          cases after with
          | single => cases finish
          | cons transparent after =>
            cases transparent with
            | transparent w d middle =>
              cases after with
              | single => cases finish
              | cons last after =>
                cases last with
                | node node p q lambdaRule =>
                  cases q with
                  | inl u => cases u; exact False.elim (lambdaRule.distinct rfl)
                  | inr q =>
                    cases q
                    · exact False.elim (lambdaRule.no_binding.2 rfl)
                    · cases after with
                      | cons turn after =>
                        cases turn with
                        | node node p q bad => exact False.elim (bad.no_binding.1 rfl)
                      | single =>
                        have same := lambdaRule.proper_context
                        cases same
                        let binding : BindingLoop site.net sourceLoop b b :=
                          ⟨.inr (.inr ()),rfl,lamBody,lamBind,HEq.rfl,HEq.rfl,rfl,rfl,.single _ _,.single _,fun _ _ => rfl⟩
                        exact ⟨sourcePre branch,sourceLoop,b,binding,rfl,rfl,rfl,
                          .cons (.node _ _ _ rule) (.cons (.transparent _ _ _) (.single _ _))⟩

abbrev c := cutFragment site.net (pathPartition schema Unit) site.closed
abbrev r := fanRight .lam 2 3
abbrev first (branch : Bool) : Endpoint c := .inr (.inl (.inl (.inl branch)))
abbrev bodyExit : Endpoint c := .inr (.inl (.inr (.inr true)))
def crossing (branch : Bool) (a : Context) : LocalPath r (.inl branch) (.inr true) a (InitialOffsets.fanAt 2 branch a) where
  edges := fanCrossEdges branch true
  start := rfl
  finish := rfl
  labeling := .cons (LabelledTurn.node (g:=r) (.inl branch) (.inl ()) lamBody (.direct (.lamBody a)))
    (.cons (LabelledTurn.node (g:=r) (.inr true) (.inr branch) (.inl ())
      (.direct (InitialOffsets.Event.apply_rel (.fan 2 branch) a))) (.single _ _))
abbrev bindInside (branch : Bool) : List (Endpoint r) :=
  [.inr (.inl (.inr false)),.inl ⟨.inr false,.inr branch⟩]
def preRaw (branch : Bool) : List (PlugSegment c r) :=
  Sum.inl (first branch)::((fanCrossEdges (f:=.lam) (i:=2) (j:=3) branch true).map Sum.inr++[Sum.inl bodyExit])
def raw (branch : Bool) : List (PlugSegment c r) := preRaw branch++(bindInside branch).map Sum.inr

def pending (branch : Bool) (a : Context) : PendingRhsBlock c r (raw branch) a a where
  pre := preRaw branch
  last := bodyExit
  enter := .inr false
  middle := InitialOffsets.fanAt 2 branch a
  inside := bindInside branch
  equation := rfl
  prefixPath := .through (crossing branch a) rfl (.single bodyExit _)
  prefixHead := rfl
  prefixLast := rfl
  arrival := rfl
  insideHead := rfl
  insideLabels := .cons (LabelledTurn.node (g:=r) (.inr false) (.inl ()) (.inr branch)
    (.inverse (InitialOffsets.Event.apply_rel (.fan 2 branch) a))) (.single _ _)

abbrev targetEdges (branch : Bool) : List (Endpoint site.reduce) := (raw branch).map (plugEnd (c).label (r).label)
theorem target_labels (branch : Bool) (a : Context) : Labelling site.reduce (targetEdges branch) a a :=
  ((pending branch a).labelling c r).actual c r

/-- Both genuine copied branches consume the FULL action Transparency
theorem. Source T was independently proved above, without I/Matches/reachability
premises. The target loop crosses two new fans and their actual glue wires. -/
theorem actual_copied_transparency (branch : Bool) (a : Context) :
    ∃ (pre loop : List (Endpoint site.reduce)) (middle : Context) (binding : BindingLoop site.reduce loop middle a),
      targetEdges branch=pre++loop ∧binding.binder=.inr (.inl branch) ∧
      pre.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),(.inl ())⟩)) ∧
      Labelling site.reduce pre a middle := by
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have labels := target_labels branch a
  have forward := labels.root_forward_of_flow newFlow (.inl branch) rfl rfl
  exact (site.action_transparency (.fan .lam 2 3 (by decide)) flow (.inl branch) rfl (source_transparency branch))
    (targetEdges branch) a a (.inr (.inl branch)) (.inl ()) lamBody lamBind rfl HEq.rfl HEq.rfl HEq.rfl
      rfl rfl forward labels

example (branch : Bool) : (targetEdges branch).length=7 := rfl
theorem new_writer_really_changes (branch : Bool) :
    InitialOffsets.fanAt 2 branch (Context.empty.cons (.star .empty))≠Context.empty.cons (.star .empty) := by
  intro same
  have atLevel := congrArg (fun x : Context => x.get 2) same
  cases branch <;> cases atLevel
theorem wrong_copy_shell : ¬Context.SameShell 3
    (InitialOffsets.fanAt 2 false Context.empty) (InitialOffsets.fanAt 2 true Context.empty) := by
  intro shell
  have wrong := shell 2 (by decide)
  cases wrong

#print axioms source_transparency
#print axioms source_labels
#print axioms target_labels
#print axioms actual_copied_transparency
#print axioms new_writer_really_changes
#print axioms wrong_copy_shell
#print axioms ActionCanonicalBlocks.split_lambda_occurrence
#print axioms ActionLambdaOccurrence.prefix_writer
#print axioms ActionLambdaCopy.binding_shell
#print axioms PathSite.pending_copied_lambda_transparency
#print axioms PathSite.action_transparency
#print axioms PathSite.transparency
#print axioms GraphStep.transparency
end Lamping.Checks.SoundnessCopiedTransparency



namespace Lamping.Checks.SoundnessUnpairedBeta
open AG Graph
private def kept : Unit → Label signature := fun _ => label .lam 1
/-- Synthetic finite site: the retained body enters the deleted binding port
before any forward beta crossing. No initial/reachable/invariant claim is made. -/
def site : PathSite (.beta 0) kept (B:=Unit) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl _,.inl _⟩ => .inl ⟨.inr (.inl ()),.inr true⟩
      | .inl ⟨.inl _,.inr true⟩ => .inl ⟨.inr (.inr ()),.inr false⟩
      | .inl ⟨.inl _,.inr false⟩ => .inl ⟨.inr (.inr ()),.inr true⟩
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inl _),.inr true⟩ => .inl ⟨.inl (),.inl ()⟩
      | .inl ⟨.inr (.inl _),.inr false⟩ => .inr (.inl ())
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inr _),.inr true⟩ => .inl ⟨.inl (),.inr false⟩
      | .inl ⟨.inr (.inr _),.inr false⟩ => .inl ⟨.inl (),.inr true⟩
      | .inr (.inl _) => .inl ⟨.inr (.inl ()),.inr false⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨u|(u|u),p⟩ | (u | ⟨w|v,d⟩))
      · cases p with | inl u => rfl | inr b => cases b <;> rfl
      · cases p with | inl u => rfl | inr b => cases b <;> rfl
      · cases p with | inl u => rfl | inr b => cases b <;> rfl
      · rfl
      · exact nomatch w
      · cases d <;> rfl
    fixedPointFree := by
      rintro (⟨u|(u|u),p⟩ | (u | ⟨w|v,d⟩)) same
      · cases p with | inl u => cases same | inr b => cases b <;> cases same
      · cases p with | inl u => cases same | inr b => cases b <;> cases same
      · cases p with | inl u => cases same | inr b => cases b <;> cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases b <;> rfl

def flow : FlowBalance site.net (fun _ => true) where
  nodes := fun _ => true
  vertices := fun | .inl w => nomatch w | .inr _ => false
  wiring := by
    rintro (⟨u|(u|u),p⟩ | (u | ⟨w|v,d⟩))
    · cases p with | inl u => rfl | inr b => cases b <;> rfl
    · cases p with | inl u => rfl | inr b => cases b <;> rfl
    · cases p with | inl u => rfl | inr b => cases b <;> rfl
    · rfl
    · exact nomatch w
    · cases d <;> rfl

abbrev body : Endpoint site.reduce := .inl ⟨.inl (),lamBody⟩
abbrev ctx : Endpoint site.reduce := .inl ⟨.inl (),(.inl ())⟩
def path : List (Endpoint site.reduce) :=
  [body,.inr (.inr (.inr (.inr false),true)),.inr (.inr (.inr (.inl true),false))]
theorem labels (a : Context) : Labelling site.reduce path a a :=
  .cons (LabelledTurn.transparent (g:=site.reduce) (.inr (.inr false)) false a)
    (.cons (LabelledTurn.transparent (g:=site.reduce) (.inr (.inl true)) true a) (.single _ _))

theorem nonroot : path.head? ≠ some (.inr (.inl ())) := by intro same; cases same

theorem proper_ancestor (a : Context) :
    ∃ (edge : BetaEdge site.net) (old : List (Endpoint site.net)) (first last : Endpoint site.net),
      SiteBetaGeometry site edge ∧ BetaPathResidual site edge (path.map (plugEnd _ _).invFun) old ∧
      ExpandedLabelling site.net old a a ∧ ExpandedForward site.net old ∧
      old.head?=some first ∧ old.getLast?=some (site.net.wire last) ∧
      AtProperRole site.net () first .lamBody 1 ∧ AtProperRole site.net () last .lamCtx 1 :=
  site.beta_proper_ancestor flow () rfl (labels a) rfl rfl
    (AtProperRole.lamBody (g:=site.reduce) (root:=()) (.inl ()) lamBody 1 rfl HEq.rfl) trivial
    (AtProperRole.lamCtx (g:=site.reduce) (root:=()) (.inl ()) (Sum.inl ()) 1 rfl HEq.rfl)

theorem actual_unpaired_stream (a : Context) :
    ∃ (edge : BetaEdge site.net) (old : List (Endpoint site.net)) (count : Nat),
      BetaPathResidual site edge (path.map (plugEnd _ _).invFun) old ∧
      BetaDetourBlocks site.net old a a count ∧ 0<count := by
  obtain ⟨edge,old,first,last,geometry,relation,oldLabels,forward,head,finish,source,target⟩ := proper_ancestor a
  obtain ⟨count,stream⟩ := relation.detour_blocks site geometry ((labels a).plug_decomposition _ _)
  have entry : (.inr (.inr (.inl (.inr false)))) ∈ path.map (plugEnd _ _).invFun := by
    exact List.mem_map.mpr ⟨.inr (.inr (.inr (.inr false),true)),by simp [path],rfl⟩
  exact ⟨edge,old,count,relation,stream,
    stream.proper_positive_count flow rfl head source trivial edge (relation.reverse_occurs site entry)⟩

#print axioms PathSite.beta_proper_ancestor
#print axioms BetaDetourBlocks.first_backward_proper_inputs
#print axioms actual_unpaired_stream
#print axioms proper_ancestor
#print axioms labels
#print axioms nonroot
end Lamping.Checks.SoundnessUnpairedBeta



namespace Lamping.Checks.SoundnessUnpairedSeam
open AG Graph
open SoundnessControlTransfer
/-- These are two actual primitive programs, not a whole-graph I counterexample.
The Cro1 head accepts replace0; the Fan0 suffix accepts replace1. Their
concatenation still does not accept replace0. -/
theorem head_total (replacement : Context) :
    ∃ middle, Traversal 1 (.op .cro) (.inr ()) (.inl ())
      (oldO.replace 0 replacement) middle :=
  ⟨_,.direct (InitialOffsets.Event.apply_rel (.cro 1) _)⟩

theorem reference_suffix : ∃ output, Traversal 0 (.op .fan) (.inl ()) fanO
    (InitialOffsets.croAt 1 oldO) output :=
  old_inverse.control_inverse_transfer (Or.inl rfl) _ rfl

theorem argument_total (replacement : Context) : ∃ output,
    Traversal 0 (.op .fan) (.inl ()) fanO
      ((InitialOffsets.croAt 1 oldO).replace 1 replacement) output := by
  obtain ⟨output,rule⟩ := reference_suffix
  exact rule.control_inverse_transfer (Or.inl rfl) _ (Context.replace_low _ _ (by decide : 0<1))

theorem no_join_after_empty : ¬∃ middle output,
    Traversal 1 (.op .cro) (.inr ()) (.inl ()) (oldO.replace 0 Context.empty) middle ∧
    Traversal 0 (.op .fan) (.inl ()) fanO middle output := by
  rintro ⟨middle,output,headRule,argRule⟩
  have unique := headRule.output_unique (Traversal.direct (InitialOffsets.Event.apply_rel (.cro 1) _))
  rw [unique] at argRule
  have marker := argRule.fan_marker
  simp [InitialOffsets.Event.apply,InitialOffsets.croAt,Context.replace_zero,FanEdgeMarker,AG.fanO] at marker

#print axioms head_total
#print axioms argument_total
#print axioms no_join_after_empty
end Lamping.Checks.SoundnessUnpairedSeam


namespace Lamping.Checks.SoundnessBetaForwardInputs
open AG Graph Lambda
open SoundnessBetaAncestor SoundnessBetaBindingTransport SoundnessBetaTransparency
/-- The production arbitrary-proper-source theorem consumes the actual Closed
initial I transported to this literal beta site, not a fixture oracle. -/
theorem actual_nonroot_inputs (a replacement : Context) : ∃ output,
    Labelling actualBetaSite.reduce targetLoop (a.replace 1 replacement) output := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have indep := (betaEncodingIso.ordinaryInvariants (encode_closed_ordinary_invariants identityApp closed 0)).independence
  apply actualBetaSite.beta_no_binding_proper_inputs actualFlow (.inl ()) rfl indep
    (target_loop_labels a) rfl rfl
    (AtProperRole.lamBody (g:=actualBetaSite.reduce) (root:=.inl ()) (.inl retainedLambda) lamBody 1 rfl HEq.rfl)
    trivial (AtProperRole.lamBind (g:=actualBetaSite.reduce) (root:=.inl ())
      (.inl retainedLambda) lamBind 1 rfl HEq.rfl) trivial ?_ replacement
  change _ ∉ ((cutLoop.map Sum.inl).map (plugEnd SoundnessBetaBindingTransport.cut.label rhs.label)).map
    (plugEnd SoundnessBetaBindingTransport.cut.label rhs.label).invFun
  simp only [List.map_map,Function.comp_def,Bij.left_inv]
  simp [cutLoop]

open SoundnessUnpairedBeta in
abbrev forwardShortcut : List (Endpoint SoundnessUnpairedBeta.site.reduce) :=
  [.inr (.inl ()),.inr (.inr (.inr (.inl false),true)),.inr (.inr (.inr (.inr true),false))]

theorem forward_shortcut_labels (a : Context) :
    Labelling SoundnessUnpairedBeta.site.reduce forwardShortcut a a :=
  .cons (LabelledTurn.transparent (g:=SoundnessUnpairedBeta.site.reduce) (.inr (.inl false)) false a)
    (.cons (LabelledTurn.transparent (g:=SoundnessUnpairedBeta.site.reduce) (.inr (.inr true)) true a) (.single _ _))

/-- A real context shortcut reflects to an ordinary principal traversal. This
is distinct from the neighbouring binding shortcut's positive-count fixture. -/
theorem context_shortcut_is_ordinary (a : Context) : ∃ old,
    Labelling SoundnessUnpairedBeta.site.net old a a := by
  let s := SoundnessUnpairedBeta.site
  obtain ⟨edge,old,first,last,geometry,relation,_,_,_,_,_,_⟩ :=
    s.beta_proper_ancestor SoundnessUnpairedBeta.flow () rfl (forward_shortcut_labels a) rfl rfl
      (AtProperRole.root (g:=s.reduce) (root:=())) trivial
      (AtProperRole.lamBind (g:=s.reduce) (root:=()) (.inl ()) lamBind 1 rfl HEq.rfl)
  refine ⟨old,relation.ordinary_without_binding s geometry ((forward_shortcut_labels a).plug_decomposition _ _) ?_⟩
  change (Sum.inr (Sum.inr (Sum.inl (Sum.inr false))) :
    PlugSegment (cutFragment s.net (pathPartition (.beta 0) Unit) s.closed) (Schema.beta 0).right.net) ∉
    [Sum.inl (.inr (.inl (.inl ()))),Sum.inr (.inr (.inl (.inl false))),
    Sum.inl (.inr (.inl (.inr (.inr true))))]
  simp

#print axioms PathSite.beta_no_binding_proper_inputs
#print axioms actual_nonroot_inputs
#print axioms context_shortcut_is_ordinary
end Lamping.Checks.SoundnessBetaForwardInputs



namespace Lamping.Checks.SoundnessRootInputs
open AG Graph Lambda

theorem identity_inputs : RootInputs Soundness.identityNet (.inl ()) :=
  (encode_closed_independence (.lam (.var 0)) (Nat.zero_lt_succ 0) 0).rootInputs

theorem existing_variable_all_inputs (requested : Context) : ∃ output,
    Labelling Soundness.identityNet Soundness.identityVariableEdges requested output :=
  identity_inputs.access Soundness.identityVariableAccess requested

/-- The weak interface has the same typed-terminal restriction as its source:
it can hold while an existing control-ended partial path rejects an input. -/
theorem partial_typed_root_inputs : RootInputs SoundnessPartialInput.graph SoundnessPartialInput.inputBoundary :=
  SoundnessPartialInput.ordinary_properties.independence.rootInputs

theorem weak_inputs_do_not_complete_control_paths :
    RootInputs SoundnessPartialInput.graph SoundnessPartialInput.inputBoundary ∧
      ¬∃ output,Labelling SoundnessPartialInput.graph SoundnessPartialInput.edges
        (Context.empty.cons (.star .empty)) output :=
  ⟨partial_typed_root_inputs,SoundnessPartialInput.no_star_input⟩

#print axioms Independence.rootInputs
#print axioms RootInputs.access
#print axioms IndexedLevelBalance.relabel_app_prefix
#print axioms NetIso.rootInputs
#print axioms existing_variable_all_inputs
#print axioms weak_inputs_do_not_complete_control_paths
end Lamping.Checks.SoundnessRootInputs


namespace Lamping.Checks.SoundnessRootBinder
open AG AG.Marker Graph Lambda SoundnessInitialInsertion
/-- The level3 nontrivial shell is retained with only the new root-input
interface supplied to the occurrence theorem. -/
theorem actual_nonzero_root_binder (newInput newMiddle newOutput : Context)
    (labels : Labelling (encode 3 identityApp).net
      (pre 3++(edge 3).principal++loopEdges 3) newInput newOutput)
    (prefixLabels : Labelling (encode 3 identityApp).net
      (pre 3++(edge 3).principal) newInput newMiddle) :
    Context.SameShell 3 newMiddle newOutput := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have invariants := encode_closed_ordinary_invariants identityApp closed 3
  have originalPrefix : Labelling (encode 3 identityApp).net
      (pre 3++(edge 3).principal) (input 3) (input 3) :=
    .cons ((edge 3).app_fun_turn (input 3))
      (.cons (LabelledTurn.transparent (g:=(encode 3 identityApp).net) (.inr (.inl (.inl ()))) false (input 3)) (.single _ _))
  have finish : (pre 3++(edge 3).principal++loopEdges 3).getLast?=
      some ((encode 3 identityApp).net.wire (.inl ⟨(edge 3).lam,(edge 3).lamBind⟩)) := by
    simp only [List.getLast?_append,(actualLoop 3).finish,Option.some_or]
    rfl
  exact binder_shell_stable_rootInputs invariants.independence.rootInputs invariants.nesting invariants.transparency
    (edge 3) _ (pre 3++(edge 3).principal) (loopEdges 3) (input 3) (input 3) (output 3)
    rfl (bodyForward 3) finish ((bodyLabels 3).ordinary_of_forward _ (bodyForward 3))
    rfl originalPrefix rfl actual_shell newInput newMiddle newOutput labels prefixLabels

#print axioms binder_shell_stable_node_rootInputs
#print axioms binder_shell_stable_rootInputs
#print axioms actual_nonzero_root_binder
end Lamping.Checks.SoundnessRootBinder


namespace Lamping.Checks.SoundnessIndexedBeta
open AG Graph Lambda SoundnessBetaAncestor
/-- A genuine nine-segment beta path obtains its coherent ancestor from
source Flow/indexed balance/T; full ordinary I is not an argument. -/
theorem actual_indexed_coherent (a : Context) :
    ∃ old : List (Endpoint actualBetaSite.net),
      CoherentExpandedCore actualBetaSite.net (.inl ()) old a (a.cons .empty) := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨initial⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initial
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  obtain ⟨edge,old,geometry,relation,labels,head,finish⟩ := actual_ancestor a
  obtain ⟨count,stream⟩ := relation.detour_blocks actualBetaSite geometry ((reduced_labels a).plug_decomposition _ _)
  exact ⟨old,stream.coherent_indexed actualFlow rfl balance rfl transparency head⟩

#print axioms BetaDetourBlocks.coherent_indexed
#print axioms IndexedLevelBalance.reflect_lambda_prefix
#print axioms actual_indexed_coherent
end Lamping.Checks.SoundnessIndexedBeta


namespace Lamping.Checks.SoundnessIndexedPairedTransparency
open AG Graph Lambda SoundnessBetaAncestor SoundnessBetaBindingTransport SoundnessBetaTransparency
/-- The real thirteen-segment reduced path forces a nonempty reverse beta
block; its SAME-assignment binder decomposition now consumes only source
Flow/indexed balance/T, not full I, N, root-input existence or Matches. -/theorem actual_indexed_binding_stream (a : Context) :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net)) (count : Nat)
      (pre loop : List (Endpoint actualBetaSite.net)) (middle : Context)
      (binding : ExpandedBindingLoop actualBetaSite.net loop middle (finalContext a)),
      BetaPathResidual actualBetaSite edge (bindingPath.map (plugEnd _ _).invFun) old ∧
      BetaDetourBlocks actualBetaSite.net old a (finalContext a) count ∧ 0<count ∧
      old=pre++loop ∧ binding.binder=.inl retainedLambda ∧
      pre.getLast?=some (actualBetaSite.net.wire (.inl ⟨.inl retainedLambda,(.inl ())⟩)) ∧
      ExpandedLabelling actualBetaSite.net pre a middle := by
  obtain ⟨edge,old,geometry,relation,_labels,first,last⟩ :=
    actualBetaSite.beta_root_ancestor actualFlow (.inl ()) rfl (binding_path_labels a) rfl bindingLast rfl
  obtain ⟨count,stream⟩ := relation.detour_blocks actualBetaSite geometry ((binding_path_labels a).plug_decomposition _ _)
  have entry : (.inr (.inr (.inl (.inr false)))) ∈ bindingPath.map (plugEnd _ _).invFun := by
    exact List.mem_map.mpr ⟨.inr (.inr (.inr (.inr false),true)),by simp [bindingPath,reduced],rfl⟩
  have positive := stream.positive_count actualBetaSite.net actualFlow (.inl ()) rfl first edge
    (relation.reverse_occurs actualBetaSite entry)
  have oldFinish : old.getLast?=some (actualBetaSite.net.wire (.inl ⟨.inl retainedLambda,lamBind⟩)) := by
    rw [←actualBetaSite.outsideEnd_wire] at last
    exact last
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨initial⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initial
  have oldT := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  obtain ⟨pre,loop,middle,binding,split,binderEq,preEnd,preLabels⟩ := stream.transparency_indexed actualFlow rfl
    balance rfl oldT (.inl retainedLambda) (.inl ()) lamBody lamBind
    rfl HEq.rfl HEq.rfl HEq.rfl first oldFinish
  exact ⟨edge,old,count,pre,loop,middle,binding,relation,stream,positive,split,binderEq,preEnd,preLabels⟩

#print axioms BetaEdge.transparency_splice_indexed
#print axioms BetaDetourBlocks.transparency_indexed
#print axioms actual_indexed_binding_stream
end Lamping.Checks.SoundnessIndexedPairedTransparency


namespace Lamping.Checks.SoundnessReachableTransparency
open AG Graph Lambda SoundnessBetaAncestor SoundnessBetaBindingTransport SoundnessBetaTransparency

theorem actual_closed_beta_trace : GraphTrace (ActualNet.initial identityApp)
    (ActualNet.ofNet actualBetaSite.reduce) [.beta 0] :=
  .single (.atSite betaKeptLabels actualBetaSite betaEncodingIso (.refl _))

/-- An actual initial-to-reduced graph trace, rather than a chosen source
invariant bundle, supplies target T through the new unconditional corollary. -/
theorem actual_trace_transparency : Transparency actualBetaSite.reduce (.inl ()) :=
  initial_trace_transparency identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
    (ActualNet.ofNet actualBetaSite.reduce) [.beta 0] actual_closed_beta_trace

/-- The genuine thirteen-segment changing-context path consumes the trace
result and retains its original input, output and physical retained binder. -/
theorem actual_binding_from_trace (a : Context) :
    ∃ (pre loop : List (Endpoint actualBetaSite.reduce)) (middle : Context)
      (binding : BindingLoop actualBetaSite.reduce loop middle (finalContext a)),
      bindingPath=pre++loop ∧binding.binder=.inl retainedLambda ∧
      pre.getLast?=some (actualBetaSite.reduce.wire (.inl ⟨.inl retainedLambda,(.inl ())⟩)) ∧
      Labelling actualBetaSite.reduce pre a middle := by
  obtain ⟨flow⟩ := actual_closed_beta_trace.flowBalance
    (betaEncodingIso.symm.flowBalance actualFlow)
  have forward := (binding_path_labels a).root_forward_of_flow flow (.inl ()) rfl rfl
  exact actual_trace_transparency bindingPath a (finalContext a) (.inl retainedLambda)
    (.inl ()) lamBody lamBind rfl HEq.rfl HEq.rfl HEq.rfl rfl rfl forward (binding_path_labels a)

#print axioms PathSite.beta_transparency_indexed
#print axioms PathSite.transparency_indexed
#print axioms GraphStep.transparency_indexed
#print axioms GraphTrace.transparency_indexed
#print axioms initial_trace_transparency
#print axioms actual_closed_beta_trace
#print axioms actual_trace_transparency
#print axioms actual_binding_from_trace
end Lamping.Checks.SoundnessReachableTransparency


namespace Lamping.Checks.SoundnessRootBetaInputs
open AG Graph Lambda SoundnessBetaAncestor SoundnessBetaBindingTransport SoundnessBetaTransparency
/-- The initial root-input base, source T and indexed balance are transported
independently to the actual beta site. No full-I argument is passed to beta. -/
theorem actual_beta_rootInputs : RootInputs actualBetaSite.reduce (.inl ()) := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  obtain ⟨initial⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initial
  have sourceInputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  have sourceT := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  exact actualBetaSite.beta_rootInputs actualFlow (.inl ()) rfl balance rfl sourceInputs sourceT

/-- The same thirteen-segment path with a real backward beta block accepts
an arbitrary newly supplied root input through the new preservation theorem. -/
theorem actual_binding_all_inputs (requested : Context) : ∃ result,
    Labelling actualBetaSite.reduce bindingPath requested result := by
  obtain ⟨flow⟩ := actualBetaSite.reduce_flowBalance actualFlow
  have reference := binding_path_labels Context.empty
  have forward := reference.root_forward_of_flow flow (.inl ()) rfl rfl
  exact actual_beta_rootInputs bindingPath Context.empty (finalContext Context.empty)
    (.inl ⟨.inl retainedLambda,lamBind⟩) .lamBind 1 reference forward rfl rfl
    (AtProperRole.lamBind (g:=actualBetaSite.reduce) (root:=.inl ())
      (.inl retainedLambda) lamBind 1 rfl HEq.rfl) trivial requested

#print axioms BetaDetourBlocks.typed_root_inputs_indexed
#print axioms BetaDetourBlocks.typed_prefix_inputs_indexed
#print axioms PathSite.beta_rootInputs
#print axioms actual_beta_rootInputs
#print axioms actual_binding_all_inputs
end Lamping.Checks.SoundnessRootBetaInputs


namespace Lamping.Checks.SoundnessRootMatchedInputs
open AG Graph Lambda SoundnessInitialInsertion SoundnessMatchingChildren
/-- The weak constructor entry uses a real Closed source Matches and root
input base. The resulting suffix is the independently specified physical
function route, including its nonzero encoding level. -/
theorem actual_function_suffix_input_root (requested : Context) :
    ∃ (child : RootAccess (encode 3 identityApp).net (.inl ()))
      (tail : List (Endpoint (encode 3 identityApp).net)),
      child=functionAccess ∧child.val=parentAccess.val++(edge 3).funEnd::tail ∧
      Labelling (encode 3 identityApp).net ((edge 3).funEnd::tail) requested requested := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching := encode_closed_matches identityApp closed 3
  have rootInputs := (encode_closed_independence identityApp closed 3).rootInputs
  obtain ⟨child,tail,split,word,_,inputs⟩ := matching.function_child_input_root rootInputs parentAccess
    (edge 3).app (edge 3).appCtx (edge 3).appFun 3 rfl HEq.rfl HEq.rfl rfl
  have same : child=functionAccess := matching.accessWord_injective (by exact word)
  obtain ⟨output,full,suffixLabels⟩ := inputs requested requested (.single _ _)
  have literal : Labelling (encode 3 identityApp).net functionAccess.val requested requested :=
    .cons ((edge 3).app_fun_turn requested)
      (.cons (LabelledTurn.transparent (g:=(encode 3 identityApp).net)
        (.inr (.inl (.inl ()))) false requested) (.single _ _))
  rw [←same] at literal
  have outputEq := full.output_unique literal
  rw [outputEq] at suffixLabels
  exact ⟨child,tail,same,split,suffixLabels⟩

#print axioms Matches.function_child_input_root
#print axioms PathSite.binding_control_input_stable_root
#print axioms PathSite.action_typed_root_inputs_weak
#print axioms PathSite.action_rootInputs
#print axioms actual_function_suffix_input_root
end Lamping.Checks.SoundnessRootMatchedInputs



namespace Lamping.Checks.SoundnessSourceActionBranch
#print axioms AG.PathSite.source_control_branch
#print axioms AG.PathSite.fan_source_passive_branch
#print axioms AG.PathSite.cro_source_passive_branch
#print axioms AG.PathSite.bra_source_passive_branch
#print axioms AG.fanPassiveLocal
#print axioms AG.unaryPassiveLocal
end Lamping.Checks.SoundnessSourceActionBranch


namespace Lamping.Checks.SoundnessSourceActionBlocks
open AG Graph Lambda SoundnessCopiedTransparency

def principal : SiteActionPrincipal site where
  edges := [.inl ⟨.inr (.inl ()),.inl ()⟩,.inr (.inr (.inr (),true))]
  first := rfl
  last := rfl
  transparent := by
    intro e f pair
    have same : e=.inl ⟨.inr (.inl ()),.inl ()⟩ ∧f=.inr (.inr (.inr (),true)) := by
      simpa using pair
    rcases same with ⟨rfl,rfl⟩
    exact ⟨.inr (),false,rfl,rfl⟩

/-- A genuine typed terminal in the middle of the old selected action block
is retained as the lambda-context stop, rather than extended through its body. -/
theorem source_context_is_terminal (branch : Bool) (a : Context) :
    ∃ (suffix : List (Endpoint site.net)) (middle : Context),
      sourcePre branch=site.net.wire (.inl ⟨.inr (.inl ()),.inr branch⟩)::(principal.edges.dropLast++suffix) ∧
      suffix=[.inr (.inr (.inr (),true))] ∧middle=InitialOffsets.fanAt 2 branch a ∧
      Labelling site.net suffix middle middle := by
  have labels : Labelling site.net (sourcePre branch) a (InitialOffsets.fanAt 2 branch a) :=
    .cons (LabelledTurn.node (g:=site.net) (.inr (.inl ())) (.inr branch) (.inl ())
      (.direct (InitialOffsets.Event.apply_rel (.fan 2 branch) a)))
      (.cons (LabelledTurn.transparent (g:=site.net) (.inr ()) false _) (.single _ _))
  obtain ⟨suffix,middle,split,first,rule,remaining,_⟩ :=
    site.typed_action_active_prefix (Or.inl rfl) principal branch labels ⟨.lam,rfl⟩ rfl
  have suffixEq : suffix=[.inr (.inr (.inr (),true))] := by
    exact List.cons.inj (List.cons.inj split).2 |>.2.symm
  have middleEq : middle=InitialOffsets.fanAt 2 branch a :=
    rule.output_unique (.direct (InitialOffsets.Event.apply_rel (.fan 2 branch) a))
  refine ⟨suffix,middle,split,suffixEq,middleEq,?_⟩
  rw [suffixEq]
  exact .single _ _

/-- The four-segment existing binding path really has the COMPLETE crossing
alternative. Its shorter lambda-context stop is excluded by physical length. -/
theorem source_binding_complete_crossing (branch : Bool) (a : Context) :
    ∃ (q : Aux Op.lam) (rest : List (Endpoint site.net)) (middle : Context),
      sourcePre branch++sourceLoop=principal.crossing site branch q++rest ∧
      Labelling site.net (principal.crossing site branch q) a middle ∧
      Labelling site.net ((.inl ⟨.inr (.inr ()),.inr q⟩)::rest) middle (InitialOffsets.fanAt 2 branch a) := by
  rcases site.typed_action_crossing_cases (Or.inl rfl) (Or.inr rfl) principal branch
      (source_labels branch a) ⟨.var,rfl⟩ rfl with ⟨_,split,_⟩|complete
  · have lengths := congrArg List.length split
    change 4=3 at lengths
    cases lengths
  · exact complete

#print axioms Forward.actual_node_ports
#print axioms PathSite.typed_action_active_prefix
#print axioms PathSite.typed_action_crossing_cases
#print axioms PathSite.typed_passive_canonical_cases
#print axioms SourceActionRoute.expand
#print axioms source_context_is_terminal
#print axioms source_binding_complete_crossing
end Lamping.Checks.SoundnessSourceActionBlocks


namespace Lamping.Checks.SoundnessSourceWriter
open AG Graph Lambda SoundnessCopiedTransparency
/-- The selected writer suffix exposes the actual CONTROL-ended source
prefix. It is a singleton boundary departure into a fan auxiliary, and has
no proper observation; no typed-prefix certificate or completion is used. -/
theorem actual_control_prefix (branch : Bool) (a : Context) :
    ∃ (pre : List (Endpoint site.net)) (q : Bool) (middle : Context),
      sourcePre branch=pre++SoundnessSourceActionBlocks.principal.edges ∧
      pre=[.inr (.inl (.inl branch))] ∧q=branch ∧middle=a ∧
      accessKind site.net pre=none ∧
      Labelling site.net pre a middle ∧
      Traversal 2 (.op .fan) (.inr q) (.inl ()) middle (InitialOffsets.fanAt 2 branch a) := by
  have labels : Labelling site.net (sourcePre branch) a (InitialOffsets.fanAt 2 branch a) :=
    .cons (LabelledTurn.node (g:=site.net) (.inr (.inl ())) (.inr branch) (.inl ())
      (.direct (InitialOffsets.Event.apply_rel (.fan 2 branch) a)))
      (.cons (LabelledTurn.transparent (g:=site.net) (.inr ()) false _) (.single _ _))
  obtain ⟨pre,q,middle,split,_root,_last,preLabels,writer⟩ :=
    site.rooted_control_writer_suffix SoundnessSourceActionBlocks.principal labels (.inl branch) rfl rfl
  have preEq : pre=[.inr (.inl (.inl branch))] :=
    List.append_cancel_right (split.symm.trans (by rfl))
  have middleEq : middle=a := by
    rw [preEq] at preLabels
    cases preLabels
    rfl
  subst middle
  have actual : Traversal 2 (.op .fan) (.inr branch) (.inl ()) a (InitialOffsets.fanAt 2 branch a) :=
    .direct (InitialOffsets.Event.apply_rel (.fan 2 branch) a)
  have qEq : q=branch := writer.reverse.control_auxiliary_unique (Or.inl rfl) actual.reverse
  exact ⟨pre,q,a,split,preEq,qEq,rfl,by rw [preEq]; rfl,preLabels,writer⟩

#print axioms PathSite.expand_labelled_source_outside
#print axioms PathSite.action_labelled_source_outside_expansion
#print axioms PathSite.source_pending_expansion
#print axioms PathSite.source_binding_control_branch
#print axioms PathSite.fan_source_lam_access
#print axioms PathSite.cro_source_lam_access
#print axioms PathSite.bra_source_lam_access
#print axioms PathSite.fan_source_app_access
#print axioms PathSite.cro_source_app_access
#print axioms PathSite.bra_source_app_access
#print axioms PathSite.fan_source_binding_access
#print axioms PathSite.cro_source_binding_access
#print axioms PathSite.bra_source_binding_access
#print axioms PathSite.action_kept_access_forward
#print axioms PathSite.action_access_forward
#print axioms actual_control_prefix
end Lamping.Checks.SoundnessSourceWriter


namespace Lamping.Checks.SoundnessMatchingGeneratedBase
open AG Graph Lambda SoundnessInitialInsertion SoundnessMatchingChildren

abbrev actualConnection : RedexConnection (encode 3 identityApp).net where
  app := (edge 3).app
  lam := (edge 3).lam
  appPort := (edge 3).appFun
  lamPort := (edge 3).lamCtx
  appIndex := 3
  lamIndex := 3
  appLabel := rfl
  lamLabel := rfl
  appPrincipal := HEq.rfl
  lamPrincipal := HEq.rfl
  edges := (edge 3).principal
  proper := ⟨⟨Context.empty,Context.empty,
    .cons (LabelledTurn.transparent (g:=(encode 3 identityApp).net) (.inr (.inl (.inl ()))) false Context.empty) (.single _ _)⟩,
    .transparent (.inr (.inl (.inl ()))) false rfl rfl (.single _)⟩
  start := rfl
  finish := rfl
  emptyWord := rfl

def originalRedex : RedexOcc identityApp := ⟨[],by exact ⟨identityApp,rfl,True.intro⟩⟩

abbrev actualSource : ActualRedexAccess (encode 3 identityApp).net (.inl ()) originalRedex where
  connection := actualConnection
  parent := parentAccess
  child := functionAccess
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl

/-- Both premises and the ordinary loop are produced from the actual closed
source Matches, rather than the earlier hand-built insertion witnesses. -/
theorem original_generated_base :
    ∃ loop suffix : List (Endpoint (encode 3 identityApp).net),
      accessWord (encode 3 identityApp).net loop=[] ∧
      GeneratedExpandedProperPath (encode 3 identityApp).net (.inl ())
        (parentAccess.val++(edge 3).principal++loop++(edge 3).reverseRoute++[(edge 3).argEnd]++suffix) := by
  have matching := encode_closed_matches identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 3
  obtain ⟨arg,leaf,loop,suffix,a,b,binding,_arg,_body,_argWord,loopWord,_binder,_argGen,_bodyGen,inserted⟩ :=
    actualSource.generated_binding_insert_base matching (edge 3) rfl rfl rfl rfl [] rfl
  exact ⟨loop,suffix,loopWord,inserted⟩

/-- The inner lambda's variable is not bound by the outer redex lambda. -/
example : ¬subtermAt (.lam (.var 0)) [.body]=some (.var (binderDepth [.body])) := by decide

#print axioms original_generated_base
#print axioms ActualRedexAccess.bound_body_loop
#print axioms PathSite.beta_fiber_generated_insert_base
end Lamping.Checks.SoundnessMatchingGeneratedBase





namespace Lamping.Checks.SoundnessFirstBetaPositions
open AG Graph Lambda SoundnessInitialInsertion SoundnessMatchingChildren SoundnessMatchingGeneratedBase

/-- The contractum's variable lies strictly INSIDE the copied argument.
The impossible retained-body branch is eliminated by actual syntax lookup. -/
theorem contractum_variable_generated :
    ∃ (q r : Path) (loop suffix : List (Endpoint (encode 3 identityApp).net)),
      [.body]=q++r ∧ArgumentOccurrence (.var 0) q ∧
      GeneratedExpandedProperPath (encode 3 identityApp).net (.inl ())
        (parentAccess.val++(edge 3).principal++loop++(edge 3).reverseRoute++[(edge 3).argEnd]++suffix) := by
  have matching := encode_closed_matches identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 3
  let position : Position (contract (.var 0) identity) := ⟨[.body],rfl⟩
  rcases actualSource.first_contractum_generated_positions matching (edge 3) rfl rfl rfl rfl position with
    ⟨old,access,atOld,_word,_generated⟩ | ⟨q,r,descendant,loop,suffix,split,occurs,_word,_arg,_loopWord,generated⟩
  · change subtermAt (.var 0) [.body]=some old at atOld
    cases atOld
  · exact ⟨q,r,loop,suffix,split,occurs,generated⟩

#print axioms contractum_variable_generated
#print axioms ActualRedexAccess.generated_argument_position
#print axioms ActualRedexAccess.first_contractum_generated_positions
#print axioms GeneratedExpandedProperPath.nested_insert
end Lamping.Checks.SoundnessFirstBetaPositions


namespace Lamping.Checks.SoundnessFirstInsertionCoherence
open AG Graph Lambda SoundnessInitialInsertion SoundnessMatchingGeneratedBase SoundnessMatchingChildren

abbrev rootParent : RootAccess (encode 0 identityApp).net (.inl ()) :=
  ⟨pre 0,⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.app,rfl⟩⟩⟩
abbrev rootFunction : RootAccess (encode 0 identityApp).net (.inl ()) :=
  ⟨pre 0++(edge 0).principal,⟨⟨⟨Context.empty,Context.empty,
    .cons ((edge 0).app_fun_turn Context.empty)
      (.cons (LabelledTurn.transparent (g:=(encode 0 identityApp).net)
        (.inr (.inl (.inl ()))) false Context.empty) (.single _ _))⟩,
    .node (.inl (.inl ())) appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩
      (.transparent (.inr (.inl (.inl ()))) false rfl rfl (.single _))⟩,
    rfl,⟨.lam,rfl⟩⟩⟩
abbrev rootConnection : RedexConnection (encode 0 identityApp).net where
  app := (edge 0).app
  lam := (edge 0).lam
  appPort := (edge 0).appFun
  lamPort := (edge 0).lamCtx
  appIndex := 0
  lamIndex := 0
  appLabel := rfl
  lamLabel := rfl
  appPrincipal := HEq.rfl
  lamPrincipal := HEq.rfl
  edges := (edge 0).principal
  proper := ⟨⟨Context.empty,Context.empty,
    .cons (LabelledTurn.transparent (g:=(encode 0 identityApp).net)
      (.inr (.inl (.inl ()))) false Context.empty) (.single _ _)⟩,
    .transparent (.inr (.inl (.inl ()))) false rfl rfl (.single _)⟩
  start := rfl
  finish := rfl
  emptyWord := rfl
abbrev rootSource : ActualRedexAccess (encode 0 identityApp).net (.inl ()) originalRedex where
  connection := rootConnection
  parent := rootParent
  child := rootFunction
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl
/-- The actual copied variable is below the argument lambda. Every requested
root context is handled by the production coherence construction. -/
theorem copied_variable_all_inputs_coherent :
    ∃ loop suffix : List (Endpoint (encode 0 identityApp).net),
      accessWord (encode 0 identityApp).net loop=[] ∧
      ∀ requested : Context,∃ output,CoherentExpandedCore (encode 0 identityApp).net (.inl ())
        (rootParent.val++(edge 0).principal++loop++(edge 0).reverseRoute++[(edge 0).argEnd]++suffix)
        requested output := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching := encode_closed_matches identityApp closed 0
  have inputs := (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  obtain ⟨descendant,loop,suffix,a,b,binding,_word,_split,loopWord,_binder,total⟩ :=
    rootSource.coherent_argument_position matching inputs flow rfl balance rfl
      (encode_closed_transparency identityApp closed 0) (edge 0) rfl rfl rfl rfl [] rfl
      (⟨[.body],rfl⟩ : Position identity)
  exact ⟨loop,suffix,loopWord,total⟩

#print axioms copied_variable_all_inputs_coherent
#print axioms ActualRedexAccess.nested_generated_base
end Lamping.Checks.SoundnessFirstInsertionCoherence



namespace Lamping.Checks.SoundnessNestedActual
open AG Graph Lambda
abbrev innerBody : Term := .lam (.var 1)
abbrev body : Term := .app (.lam innerBody) (.var 0)
abbrev source : Term := .app (.lam body) AG.identity
abbrev graph := (encode 0 source).net
abbrev outerApp : (encode 0 source).N := .inl (.inl ())
abbrev outerLam : (encode 0 source).N := .inr (.inl (.inl ()))
abbrev innerApp : (encode 0 source).N := .inr (.inl (.inr (.inl (.inl ()))))
abbrev innerLam : (encode 0 source).N := .inr (.inl (.inr (.inr (.inl (.inl ())))))
abbrev outerW : (encode 0 source).W := .inr (.inl (.inl ()))
abbrev bodyW : (encode 0 source).W := .inl (.inr (.inl (.inr (.inl ()))))
abbrev innerW : (encode 0 source).W := .inl (.inr (.inl (.inl (.inr (.inr (.inl (.inl ())))))))
example : graph.label outerApp=AG.label .app 0 := rfl
example : graph.label outerLam=AG.label .lam 0 := rfl
example : graph.label innerApp=AG.label .app 0 := rfl
example : graph.label innerLam=AG.label .lam 0 := rfl
example : graph.wire (.inl ⟨outerApp,.inl ()⟩)=.inr (.inr (outerW,false)) := rfl
example : graph.wire (.inr (.inr (outerW,true)))=.inl ⟨outerLam,.inl ()⟩ := rfl
example : graph.wire (.inl ⟨outerLam,lamBody⟩)=.inr (.inr (bodyW,false)) := rfl
example : graph.wire (.inr (.inr (bodyW,true)))=.inl ⟨innerApp,appCtx⟩ := rfl
example : graph.wire (.inl ⟨innerApp,.inl ()⟩)=.inr (.inr (innerW,false)) := rfl
example : graph.wire (.inr (.inr (innerW,true)))=.inl ⟨innerLam,.inl ()⟩ := rfl



def outerBeta : BetaEdge graph where
  app := outerApp
  lam := outerLam
  index := 0
  appLabel := rfl
  lamLabel := rfl
  appFun := .inl ()
  appCtx := .inr false
  appArg := .inr true
  lamCtx := .inl ()
  lamBody := .inr true
  lamBind := .inr false
  appFun_role := HEq.rfl
  appCtx_role := HEq.rfl
  appArg_role := HEq.rfl
  lamCtx_role := HEq.rfl
  lamBody_role := HEq.rfl
  lamBind_role := HEq.rfl
  principal := [.inl ⟨outerApp,.inl ()⟩,.inr (.inr (outerW,true))]
  principalStart := rfl
  principalEnd := rfl
  transparent := by
    intro e f pair
    have same := List.mem_singleton.mp pair
    cases same
    exact ⟨outerW,false,rfl,rfl⟩

def innerBeta : BetaEdge graph where
  app := innerApp
  lam := innerLam
  index := 0
  appLabel := rfl
  lamLabel := rfl
  appFun := .inl ()
  appCtx := .inr false
  appArg := .inr true
  lamCtx := .inl ()
  lamBody := .inr true
  lamBind := .inr false
  appFun_role := HEq.rfl
  appCtx_role := HEq.rfl
  appArg_role := HEq.rfl
  lamCtx_role := HEq.rfl
  lamBody_role := HEq.rfl
  lamBind_role := HEq.rfl
  principal := [.inl ⟨innerApp,.inl ()⟩,.inr (.inr (innerW,true))]
  principalStart := rfl
  principalEnd := rfl
  transparent := by
    intro e f pair
    have same := List.mem_singleton.mp pair
    cases same
    exact ⟨innerW,false,rfl,rfl⟩

abbrev rootEnd : Endpoint graph := .inr (.inl (.inl ()))
abbrev outerChildEdges : List (Endpoint graph) := [rootEnd]++outerBeta.principal
abbrev innerParentEdges : List (Endpoint graph) := outerChildEdges++[.inl ⟨outerLam,lamBody⟩,.inr (.inr (bodyW,true))]
abbrev innerChildEdges : List (Endpoint graph) := innerParentEdges++innerBeta.principal

theorem outerChild_labels (a : Context) : Labelling graph outerChildEdges a a :=
  .cons (outerBeta.app_fun_turn a) (.cons (.transparent outerW false a) (.single _ _))
theorem innerParent_labels (a : Context) : Labelling graph innerParentEdges a a :=
  .cons (outerBeta.app_fun_turn a) (.cons (.transparent outerW false a)
    (.cons (LabelledTurn.node (g:=graph) outerLam (.inl ()) lamBody (.direct (.lamBody a)))
      (.cons (.transparent bodyW false a) (.single _ _))))
theorem innerChild_labels (a : Context) : Labelling graph innerChildEdges a a :=
  .cons (outerBeta.app_fun_turn a) (.cons (.transparent outerW false a)
    (.cons (LabelledTurn.node (g:=graph) outerLam (.inl ()) lamBody (.direct (.lamBody a)))
      (.cons (.transparent bodyW false a)
        (.cons (innerBeta.app_fun_turn a) (.cons (.transparent innerW false a) (.single _ _))))))

def asAccess {es : List (Endpoint graph)} (labels : Labelling graph es Context.empty Context.empty)
    (rooted : es.head?=some rootEnd) (kind : AccessKind) (finish : accessKind graph es=some kind) :
    RootAccess graph (.inl ()) := ⟨es,⟨⟨⟨_,_,labels⟩,by
      obtain ⟨flow⟩ := encode_flowBalance source 0
      exact labels.root_forward_of_flow flow (.inl ()) rooted rfl⟩,rooted,⟨kind,finish⟩⟩⟩

abbrev outerParentAccess := asAccess (.single rootEnd Context.empty) rfl .app rfl
abbrev outerChildAccess := asAccess (outerChild_labels Context.empty) rfl .lam rfl
abbrev innerParentAccess := asAccess (innerParent_labels Context.empty) rfl .app rfl
abbrev innerChildAccess := asAccess (innerChild_labels Context.empty) rfl .lam rfl

abbrev outerConnection : RedexConnection graph where
  app := outerBeta.app
  lam := outerBeta.lam
  appPort := outerBeta.appFun
  lamPort := outerBeta.lamCtx
  appIndex := 0
  lamIndex := 0
  appLabel := rfl
  lamLabel := rfl
  appPrincipal := HEq.rfl
  lamPrincipal := HEq.rfl
  edges := outerBeta.principal
  proper := ⟨⟨Context.empty,Context.empty,outerBeta.principal_labeling Context.empty⟩,
    .transparent outerW false rfl rfl (.single _)⟩
  start := rfl
  finish := rfl
  emptyWord := rfl
abbrev innerConnection : RedexConnection graph where
  app := innerBeta.app
  lam := innerBeta.lam
  appPort := innerBeta.appFun
  lamPort := innerBeta.lamCtx
  appIndex := 0
  lamIndex := 0
  appLabel := rfl
  lamLabel := rfl
  appPrincipal := HEq.rfl
  lamPrincipal := HEq.rfl
  edges := innerBeta.principal
  proper := ⟨⟨Context.empty,Context.empty,innerBeta.principal_labeling Context.empty⟩,
    .transparent innerW false rfl rfl (.single _)⟩
  start := rfl
  finish := rfl
  emptyWord := rfl

abbrev outerRedex : RedexOcc source := ⟨[],⟨source,rfl,True.intro⟩⟩
abbrev innerRedex : RedexOcc source := ⟨[.fn,.body],⟨.app (.lam innerBody) (.var 0),rfl,True.intro⟩⟩
abbrev actualOuter : ActualRedexAccess graph (.inl ()) outerRedex where
  connection := outerConnection
  parent := outerParentAccess
  child := outerChildAccess
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl
abbrev actualInner : ActualRedexAccess graph (.inl ()) innerRedex where
  connection := innerConnection
  parent := innerParentAccess
  child := innerChildAccess
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl




/-- This is a genuine inner-first, outer-second contraction with lifting:
the inner copy crosses a lambda before the outer argument is substituted. -/
theorem actual_two_steps : BetaHistory [[.fn,.body],[]] source (.lam AG.identity) :=
  .cons ⟨innerBody,.var 0,rfl,rfl⟩
    (.cons ⟨.lam (.var 1),AG.identity,rfl,rfl⟩ (.nil _))

/-- The shared prefix and BOTH ordinary loops are supplied by the real
closed encoded source Matches, not by a generatedness oracle. -/
theorem actual_nested_generated :
    ∃ pre loop tail suffix : List (Endpoint graph),
      pre.length=2 ∧
      GeneratedExpandedBindingLoop graph (.inl ()) (actualOuter.parent.val++outerBeta.principal) outerBeta.lam
        (pre++innerBeta.principal++loop++innerBeta.reverseRoute++[innerBeta.argEnd]++tail) ∧
      GeneratedExpandedProperPath graph (.inl ())
        (actualOuter.parent.val++outerBeta.principal++
          (pre++innerBeta.principal++loop++innerBeta.reverseRoute++[innerBeta.argEnd]++tail)++
          outerBeta.reverseRoute++[outerBeta.argEnd]++suffix) := by
  have closed : Closed source := by
    change ((1<3) ∧ (0<1)) ∧ (0<1)
    decide
  have matching := encode_closed_matches source closed 0
  obtain ⟨pre,loop,tail,suffix,parentSplit,loopGenerated,generated⟩ :=
    actualOuter.nested_generated_base actualInner matching outerBeta innerBeta rfl rfl rfl rfl rfl rfl
      rfl rfl [] [] [.body] rfl rfl rfl
  have lengths := congrArg List.length parentSplit
  have preLength : pre.length=2 := by
    simp only [asAccess,innerParentAccess,outerParentAccess,
      innerParentEdges,outerChildEdges,outerBeta,List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  exact ⟨pre,loop,tail,suffix,preLength,loopGenerated,generated⟩

example : (outerBeta.principal.length,innerBeta.principal.length)=(2,2) := rfl
example : outerBeta.app≠innerBeta.app := by intro impossible; cases impossible
example : binderDepth ([.body] : Path)=1 := rfl
#print axioms actual_two_steps
#print axioms actual_nested_generated
end Lamping.Checks.SoundnessNestedActual




namespace Lamping.Checks.SoundnessFirstContractumCoherence
open AG Graph Lambda SoundnessInitialInsertion SoundnessFirstInsertionCoherence

theorem copied_contractum_position_all_inputs :
    ∃ (q r : Path) (loop suffix : List (Endpoint (encode 0 identityApp).net)),
      [.body]=q++r ∧ArgumentOccurrence (.var 0) q ∧
      ∀ requested : Context,∃ output,CoherentExpandedCore (encode 0 identityApp).net (.inl ())
        (rootParent.val++(edge 0).principal++loop++(edge 0).reverseRoute++[(edge 0).argEnd]++suffix)
        requested output := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching := encode_closed_matches identityApp closed 0
  have inputs := (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  let position : Position (contract (.var 0) identity) := ⟨[.body],rfl⟩
  rcases rootSource.first_contractum_coherent_positions matching inputs flow rfl balance rfl
      (encode_closed_transparency identityApp closed 0) (edge 0) rfl rfl rfl rfl position with
    ⟨old,access,atOld,_word,_total⟩ | ⟨q,r,descendant,loop,suffix,split,occurs,_word,_arg,_loopWord,total⟩
  · change subtermAt (.var 0) [.body]=some old at atOld
    cases atOld
  · exact ⟨q,r,loop,suffix,split,occurs,total⟩

#print axioms copied_contractum_position_all_inputs
end Lamping.Checks.SoundnessFirstContractumCoherence


namespace Lamping.Checks.SoundnessNestedHistoryActual
open AG Graph Lambda SoundnessNestedActual

/-- Unlike the original nested base test, the old outer-variable premise
is DERIVED from the actual inner step and its correctly lifted copy. -/
theorem actual_history_supplies_generated :
    ∃ pre loop tail suffix : List (Endpoint graph),
      BetaHistory [[.fn,.body],[]] source (.lam AG.identity) ∧
      GeneratedExpandedProperPath graph (.inl ())
        (actualOuter.parent.val++outerBeta.principal++
          (pre++innerBeta.principal++loop++innerBeta.reverseRoute++[innerBeta.argEnd]++tail)++
          outerBeta.reverseRoute++[outerBeta.argEnd]++suffix) := by
  have closed : Closed source := by
    change ((1<3) ∧ (0<1)) ∧ (0<1)
    decide
  have matching := encode_closed_matches source closed 0
  have step : BetaAt body [] (.lam (.var 1)) := ⟨innerBody,.var 0,rfl,rfl⟩
  obtain ⟨history,pre,loop,tail,suffix,_parent,_loopGenerated,generated⟩ :=
    actualOuter.nested_history_generated actualInner matching outerBeta innerBeta rfl rfl rfl rfl rfl rfl
      rfl rfl [] [] [.body] rfl step rfl rfl
  exact ⟨pre,loop,tail,suffix,history,generated⟩

/-- Keeping the copied index 0 would bind to the wrong, inner lambda. -/
example : ¬subtermAt (.lam (.var 1)) [.body]=some (.var 0) := by decide
#print axioms actual_history_supplies_generated
end Lamping.Checks.SoundnessNestedHistoryActual

namespace Lamping.Checks.SoundnessFirstInsertionStreams
open AG Graph Lambda SoundnessInitialInsertion SoundnessFirstInsertionCoherence

theorem copied_variable_all_inputs_one_stream :
    ∃ loop suffix : List (Endpoint (encode 0 identityApp).net),
      ∀ requested : Context,∃ output,
        CoherentExpandedCore (encode 0 identityApp).net (.inl ())
          (rootParent.val++(edge 0).principal++loop++(edge 0).reverseRoute++[(edge 0).argEnd]++suffix)
          requested output ∧
        BetaDetourBlocks (encode 0 identityApp).net
          (rootParent.val++(edge 0).principal++loop++(edge 0).reverseRoute++[(edge 0).argEnd]++suffix)
          requested output 1 := by
  have closed : Closed identityApp := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
  have matching := encode_closed_matches identityApp closed 0
  have inputs := (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨flow⟩ := encode_flowBalance identityApp 0
  obtain ⟨balance⟩ := encode_indexed_balance identityApp 0
  obtain ⟨descendant,loop,suffix,a,b,binding,_word,_split,_loopWord,_binder,total⟩ :=
    rootSource.coherent_argument_position_streams matching inputs flow rfl balance rfl
      (encode_closed_transparency identityApp closed 0) (edge 0) rfl rfl rfl rfl [] rfl
      (⟨[.body],rfl⟩ : Position identity)
  exact ⟨loop,suffix,total⟩

#print axioms copied_variable_all_inputs_one_stream
end Lamping.Checks.SoundnessFirstInsertionStreams


namespace Lamping.Checks.SoundnessNestedCoherentActual
open AG Graph Lambda SoundnessNestedActual

/-- Actual nested capture, with the terminal INSIDE the original outer
argument. The same physical two-block path is coherent for EVERY input. -/
theorem actual_nested_two_streams :
    ∃ pre loop tail suffix : List (Endpoint graph),pre.length=2 ∧
      ∀ requested : Context,∃ output,
        CoherentExpandedCore graph (.inl ())
          (actualOuter.parent.val++outerBeta.principal++
            (pre++innerBeta.principal++loop++innerBeta.reverseRoute++[innerBeta.argEnd]++tail)++
            outerBeta.reverseRoute++[outerBeta.argEnd]++suffix) requested output ∧
        BetaDetourBlocks graph
          (actualOuter.parent.val++outerBeta.principal++
            (pre++innerBeta.principal++loop++innerBeta.reverseRoute++[innerBeta.argEnd]++tail)++
            outerBeta.reverseRoute++[outerBeta.argEnd]++suffix) requested output 2 := by
  have closed : Closed source := by
    change ((1<3) ∧ (0<1)) ∧ (0<1)
    decide
  have matching := encode_closed_matches source closed 0
  have inputs := (encode_closed_independence source closed 0).rootInputs
  obtain ⟨flow⟩ := encode_flowBalance source 0
  obtain ⟨balance⟩ := encode_indexed_balance source 0
  obtain ⟨pre,loop,tail,suffix,parentSplit,total⟩ :=
    actualOuter.nested_coherent_inputs actualInner matching inputs flow rfl balance rfl
      (encode_closed_transparency source closed 0) outerBeta innerBeta rfl rfl rfl rfl rfl rfl
      rfl rfl [] [] [.body] (⟨[.body],rfl⟩ : Position AG.identity) rfl rfl rfl
  have lengths := congrArg List.length parentSplit
  have preLength : pre.length=2 := by
    simp only [asAccess,innerParentAccess,outerParentAccess,
      innerParentEdges,outerChildEdges,outerBeta,List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  exact ⟨pre,loop,tail,suffix,preLength,total⟩

#print axioms actual_nested_two_streams
#print axioms RootInputs.insert_into_paired_argument
#print axioms ActualRedexAccess.nested_coherent_inputs
end Lamping.Checks.SoundnessNestedCoherentActual


namespace Lamping.Checks.SoundnessSelectedPrincipalWord
open AG Graph Lambda Lambda.Labelled SoundnessInitialInsertion SoundnessFirstInsertionCoherence
abbrev original : LTerm := initLabels identityApp

/-- ANY real shared selector chooses the actual two-segment principal for
the selected old function label; the chosen cut cannot drift to another visit. -/
theorem actual_shared_principal_word
    (selection : SourceEdgeSelection original (encode 0 identityApp).net (.inl ())) :
    selection.evalLabel (edge 0) (Labelled.Label.atom 1)=(edge 0).principal ∧
      (selection.evalLabel (edge 0) (Labelled.Label.atom 1)).length=2 := by
  have matching : Matches (encode 0 identityApp).net (.inl ()) original.erase :=
    encode_closed_matches identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 0
  obtain ⟨fragment,segments⟩ := rootSource.source_function_fragment (original:=original) matching rfl
  let cell : {e : SourceEdge // e∈sourceEdges [] .external original} := ⟨_,fragment.source_member⟩
  have same := (selection.chosen cell).2.function_segments_unique (init_is_INIT identityApp) matching fragment
  have actual : selection.evalLabel (edge 0) (Labelled.Label.atom 1)=(edge 0).principal := by
    change selection.atomWord 1=(edge 0).principal
    exact (selection.atomWord_cell (init_is_INIT identityApp) cell rfl).trans (same.trans segments)
  exact ⟨actual,by rw [actual]; rfl⟩

/-- A nonempty selected old degree is available in this actual graph fiber. -/
theorem actual_selected_degree : SelectedDegree original
    (physicalBetaFiberPaths (encode 0 identityApp).net (.inl ()) identityApp (edge 0).app (edge 0).lam)
    (Labelled.Label.atom 1) := by
  refine ⟨[],?_,rfl⟩
  exact (mem_physicalBetaFiberPaths _ _ _ _ _ _).mpr
    ⟨SoundnessMatchingGeneratedBase.originalRedex,rootSource,rfl,rfl,rfl⟩

#print axioms actual_shared_principal_word
#print axioms actual_selected_degree
#print axioms SourceEdgeFragment.function_segments_unique
#print axioms PathSite.selected_principal_word
end Lamping.Checks.SoundnessSelectedPrincipalWord

namespace Lamping.Checks.SoundnessFirstHistoryEvaluation
open AG Graph Lambda Lambda.Labelled
abbrev original : LTerm := initLabels identityApp
abbrev developed : LTerm := LTerm.contract (.atom 0) (.atom 1)
  (.var (.atom 2) 0) (.lam (.atom 3) (.var (.atom 4) 0))
private def redex : RedexOcc original.erase := ⟨[],⟨_,rfl,True.intro⟩⟩
private def parent : RootAccess actualBetaSite.net (.inl ()) :=
  ⟨[.inr (.inl (.inl ()))],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.app,rfl⟩⟩⟩
private def principal : List (Endpoint actualBetaSite.net) :=
  [.inl ⟨.inr (.inl ()),.inl ()⟩,.inr (.inr (.inr (),true))]
private theorem principalLabels (a : Context) : Labelling actualBetaSite.net principal a a :=
  .cons (LabelledTurn.transparent (g:=actualBetaSite.net) (.inr ()) false a) (.single _ _)
private theorem principalForward : Forward actualBetaSite.net principal :=
  .transparent (.inr ()) false rfl rfl (.single _)
private def childEdges : List (Endpoint actualBetaSite.net) :=
  [.inr (.inl (.inl ())),.inl ⟨.inr (.inl ()),.inl ()⟩,.inr (.inr (.inr (),true))]
private theorem childLabels : Labelling actualBetaSite.net childEdges Context.empty Context.empty :=
  .cons (LabelledTurn.node (g:=actualBetaSite.net) (.inr (.inl ())) appCtx (Sum.inl ()) (.direct (.appFun _)))
    (principalLabels _)
private def child : RootAccess actualBetaSite.net (.inl ()) :=
  ⟨childEdges,⟨⟨⟨Context.empty,Context.empty,childLabels⟩,
    .node (.inr (.inl ())) appCtx (.inl ()) rfl rfl ⟨rfl,Or.inl rfl⟩ principalForward⟩,rfl,⟨.lam,rfl⟩⟩⟩
private def connection : RedexConnection actualBetaSite.net where
  app := .inr (.inl ())
  lam := .inr (.inr ())
  appPort := .inl ()
  lamPort := .inl ()
  appIndex := 0
  lamIndex := 0
  appLabel := rfl
  lamLabel := rfl
  appPrincipal := HEq.rfl
  lamPrincipal := HEq.rfl
  edges := principal
  proper := ⟨⟨Context.empty,Context.empty,principalLabels _⟩,principalForward⟩
  start := rfl
  finish := rfl
  emptyWord := rfl
private def rich : ActualRedexAccess actualBetaSite.net (.inl ()) redex where
  connection := connection
  parent := parent
  child := child
  ctx := appCtx
  contextPrincipal := HEq.rfl
  parentWord := rfl
  childWord := rfl
  parentFinish := rfl
  split := rfl
private theorem member : []∈actualBetaSite.betaSyntaxFiber (.inl ()) original.erase :=
  (mem_physicalBetaFiberPaths _ _ _ _ _ _).mpr ⟨redex,rich,rfl,rfl,rfl⟩
private theorem actualRelative : Marked.RelativeHistory [[]]
    (Marked.mark (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase) original.erase) (.lam (.var 0)) := by
  change Marked.RelativeHistory [[]]
    (if ([] : Path)∈actualBetaSite.betaSyntaxFiber (.inl ()) original.erase then
      .red [[]] (.var 0) (.lam (.var 0)) else .app [[]] (.lam (.var 0)) (.lam (.var 0))) (.lam (.var 0))
  rw [if_pos member]
  exact .cons (.root [[]] (.var 0) (.lam (.var 0))) (.nil _)

/-- The actual one-W graph site and the real first P04 event supply ONE
selector for EVERY target position, including the copied variable inside I.
No Generated, loop, principal-word or target correctness premise is supplied. -/
theorem actual_first_relative_all_positions :
    ∃ beta : BetaEdge actualBetaSite.net,
      beta.app=.inr (.inl ()) ∧ beta.lam=.inr (.inr ()) ∧
      ∃ selection : SourceEdgeSelection original actualBetaSite.net (.inl ()),
      ∀ {p sub},developed.subterm p=some sub →
      ∃ es,developed.sourceTrail selection.atomWord beta.principal beta.reverseRoute p=some es ∧
        GeneratedExpandedProperPath actualBetaSite.net (.inl ()) es ∧
        ∃ count,count≤1 ∧∀ requested : Context,∃ output,
          CoherentExpandedCore actualBetaSite.net (.inl ()) es requested output ∧
          BetaDetourBlocks actualBetaSite.net es requested output count := by
  have closed : Closed identityApp := by change (0<1) ∧ (0<1); decide
  have matching := betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨initialBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initialBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  exact actualBetaSite.first_relative_root_evaluation (init_is_INIT identityApp) closed matching inputs
    SoundnessBetaAncestor.actualFlow rfl balance rfl transparency actualRelative

#print axioms actual_first_relative_all_positions
#print axioms PathSite.first_relative_root_evaluation
#print axioms PathSite.relative_active_principal_word
end Lamping.Checks.SoundnessFirstHistoryEvaluation

namespace Lamping.Checks.SoundnessOriginalSupportedLoops
open AG Graph Lambda Lambda.Labelled SoundnessInitialInsertion
abbrev original : LTerm := initLabels identityApp

/-- The unselected ARGUMENT lambda, rather than the beta function lambda,
already has a genuine zero-event support tree under ANY shared selector. -/
theorem actual_argument_binder_support
    (selection : SourceEdgeSelection original (encode 0 identityApp).net (.inl ())) :
    ∃ (parent : RootAccess (encode 0 identityApp).net (.inl ()))
      (loop : List (Endpoint (encode 0 identityApp).net)) (a b c : Context)
      (binding : BindingLoop (encode 0 identityApp).net loop b c),
      accessWord (encode 0 identityApp).net parent.val=[.arg] ∧
      SupportedExpandedBindingLoop (encode 0 identityApp).net (.inl ()) parent.val binding.binder loop ∧
      original.sourceTrail selection.atomWord (edge 0).principal (edge 0).reverseRoute [.arg]=some parent.val ∧
      original.sourceTrail selection.atomWord (edge 0).principal (edge 0).reverseRoute [.arg,.body]=
        some (parent.val++loop) ∧
      Labelling (encode 0 identityApp).net parent.val a b ∧
      GeneratedExpandedProperPath (encode 0 identityApp).net (.inl ()) (parent.val++loop) := by
  have matching : Matches (encode 0 identityApp).net (.inl ()) original.erase :=
    encode_closed_matches identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 0
  obtain ⟨parent,leaf,loop,a,b,c,binding,ctx,parentWord,_leafWord,split,_loopWord,labels,_role,_finish,
      parentEval,leafEval,support,_parentGen,leafGen⟩ :=
    matching.original_supported_loop (init_is_INIT identityApp) selection (edge 0)
      (p:=[.arg]) (q:=[]) rfl rfl
  exact ⟨parent,loop,a,b,c,binding,parentWord,support,parentEval,by simpa only [split] using leafEval,
    labels,by simpa only [split] using leafGen⟩

#print axioms actual_argument_binder_support
#print axioms Matches.original_supported_loop
end Lamping.Checks.SoundnessOriginalSupportedLoops

namespace Lamping.Checks.SoundnessCopiedSupportedLoops
open AG Graph Lambda Lambda.Labelled SoundnessInitialInsertion SoundnessFirstInsertionCoherence
abbrev original : LTerm := initLabels identityApp

/-- I I's copied argument lambda retains its physical binder and receives
an actual rebased support beneath the nonempty beta detour. -/
theorem actual_copied_argument_support
    (selection : SourceEdgeSelection original (encode 0 identityApp).net (.inl ())) :
    ∃ (outerLoop pre copiedLoop : List (Endpoint (encode 0 identityApp).net)),∃ binder,
      SupportedExpandedBindingLoop (encode 0 identityApp).net (.inl ())
        (rootSource.parent.val++(edge 0).principal++outerLoop++(edge 0).reverseRoute++[(edge 0).argEnd]++pre)
        binder copiedLoop ∧
      GeneratedExpandedProperPath (encode 0 identityApp).net (.inl ())
        (rootSource.parent.val++(edge 0).principal++outerLoop++(edge 0).reverseRoute++[(edge 0).argEnd]++pre++copiedLoop) := by
  have matching : Matches (encode 0 identityApp).net (.inl ()) original.erase :=
    encode_closed_matches identityApp ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩ 0
  obtain ⟨_oldParent,outerLoop,pre,copiedLoop,_a,b,c,binding,_split,_labels,_eval,_oldSupport,support,generated⟩ :=
    rootSource.copied_original_supported_loop (original:=original) matching (init_is_INIT identityApp)
      selection (edge 0) rfl rfl rfl rfl [] rfl [] rfl [] rfl
  exact ⟨outerLoop,pre,copiedLoop,binding.binder,support,generated⟩

#print axioms actual_copied_argument_support
#print axioms ActualRedexAccess.copied_original_supported_loop
end Lamping.Checks.SoundnessCopiedSupportedLoops

namespace Lamping.Checks.SoundnessFirstHistoryEvaluation
open AG Graph Lambda Lambda.Labelled

/-- The generic P-copy step is exercised on a real marked event with its
PREVIOUS P/L derived from source Matches, not passed as fixture oracles. -/
theorem actual_generated_copy_step :
    ∃ beta : BetaEdge actualBetaSite.net,
      ∃ selection : SourceEdgeSelection original actualBetaSite.net (.inl ()),∃ word,
      developed.sourceTrail selection.atomWord beta.principal beta.reverseRoute [.body]=some word ∧
      GeneratedExpandedProperPath actualBetaSite.net (.inl ()) word := by
  have closed : Closed identityApp := by change (0<1) ∧ (0<1); decide
  have initial : INIT original := init_is_INIT identityApp
  have matching : Matches actualBetaSite.net (.inl ()) original.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  obtain ⟨beta,app,lam,allPorts⟩ := actualBetaSite.selected_beta_source_ports initial matching
  let selection := matching.source_edge_selection closed
  have paths : GeneratedSyntaxPaths selection beta original := matching.generated_syntax_paths initial selection beta
  have binders : SupportedSyntaxBinders selection beta original := matching.supported_syntax_binders initial selection beta
  obtain ⟨word,eval,generated⟩ := actualBetaSite.relative_generated_copy_step initial matching
    selection beta app lam allPorts (fun route => selection.selected_route_walk initial matching allPorts route) (.nil _) actualRelative (.nil _)
    (.root (.atom 0) (.atom 1) (.var (.atom 2) 0) (.lam (.atom 3) (.var (.atom 4) 0)))
    rfl (q:=[]) (r:=[.body]) rfl rfl paths binders
  exact ⟨beta,selection,word,eval,generated⟩

#print axioms actual_generated_copy_step
#print axioms Matches.generated_syntax_paths
#print axioms Matches.supported_syntax_binders
#print axioms PathSite.relative_generated_copy_step
end Lamping.Checks.SoundnessFirstHistoryEvaluation

namespace Lamping.Checks.SoundnessFirstHistoryEvaluation
open AG Graph Lambda Lambda.Labelled

/-- The production JOINT induction consumes the real fixed-fiber marked
schedule and its existing label history. Neither intermediate invariant is
supplied by this fixture. The target lambda has a real bound variable. -/
theorem actual_joint_history :
    ∃ beta : BetaEdge actualBetaSite.net,
      ∃ selection : SourceEdgeSelection original actualBetaSite.net (.inl ()),
      GeneratedSyntaxPaths selection beta developed ∧SupportedSyntaxBinders selection beta developed := by
  have closed : Closed identityApp := by change (0<1) ∧ (0<1); decide
  have matching : Matches actualBetaSite.net (.inl ()) original.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  obtain ⟨beta,_app,_lam,selection,joint⟩ := actualBetaSite.relative_history_generated (init_is_INIT identityApp) closed matching
  have labels : History [[]] original developed := .cons (.root _ _ _ _) (.nil _)
  have result := joint actualRelative labels
  exact ⟨beta,selection,result⟩

/-- A concrete bound leaf consumes the L result of the actual finite-history
induction, including its literal root ambient and nonempty copied detour. -/
theorem actual_joint_target_binding :
    ∃ (beta : BetaEdge actualBetaSite.net)
      (selection : SourceEdgeSelection original actualBetaSite.net (.inl ()))
      (ambient loop : List (Endpoint actualBetaSite.net)),∃ binder,
      developed.sourceTrail selection.atomWord beta.principal beta.reverseRoute []=some ambient ∧
      developed.sourceTrail selection.atomWord beta.principal beta.reverseRoute [.body]=some (ambient++loop) ∧
      SupportedExpandedBindingLoop actualBetaSite.net (.inl ()) ambient binder loop := by
  obtain ⟨beta,selection,_paths,binders⟩ := actual_joint_history
  obtain ⟨ambient,loop,binder,_ctx,ambientEval,leafEval,support,_shape,_role,_finish⟩ :=
    binders (p:=[]) (stamp:=developed.label) (body:=.var (.atom 4) 0) (q:=[]) rfl rfl
  exact ⟨beta,selection,ambient,loop,binder,ambientEval,leafEval,support⟩

/-- The existing two-redex nested example uses two physical pairs. It may
not be substituted for a two-event development of this ONE fixed pair. -/
theorem nested_fixture_pairs_are_distinct :
    SoundnessNestedActual.outerBeta.app≠SoundnessNestedActual.innerBeta.app := by
  intro impossible
  cases impossible

#print axioms actual_joint_history
#print axioms actual_joint_target_binding
#print axioms nested_fixture_pairs_are_distinct
#print axioms PathSite.relative_generated_paths_step
#print axioms PathSite.relative_supported_binders_step
#print axioms PathSite.relative_history_generated
end Lamping.Checks.SoundnessFirstHistoryEvaluation

namespace Lamping.Checks.SoundnessFirstHistoryEvaluation
open AG Graph Lambda Lambda.Labelled
/-- The actual full Q step consumes the real marked I I event. Its OLD Q,
L and R are proved from the concrete source Matches, never supplied as
fixture oracles. The copied variable has a complete paired path for EVERY
requested root context. This is one actual step, not typed history closure. -/
theorem actual_typed_path_step :
    ∃ (beta : BetaEdge actualBetaSite.net)
      (selection : SourceEdgeSelection original actualBetaSite.net (.inl ())),
      TypedSyntaxPaths selection beta developed := by
  have closed : Closed identityApp := by change (0<1) ∧ (0<1); decide
  have initial : INIT original := init_is_INIT identityApp
  have matching : Matches actualBetaSite.net (.inl ()) original.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨initialBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initialBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  obtain ⟨beta,app,lam,allPorts⟩ := actualBetaSite.selected_beta_source_ports initial matching
  let selection := matching.source_edge_selection closed
  have paths : TypedSyntaxPaths selection beta original := matching.typed_syntax_paths initial inputs selection beta
  have binders : SupportedSyntaxBinders selection beta original := matching.supported_syntax_binders initial selection beta
  have typedBinders : TypedSyntaxBinders selection beta original := matching.typed_syntax_binders initial transparency selection beta
  have result : TypedSyntaxPaths selection beta developed := actualBetaSite.relative_typed_paths_step initial matching
    selection beta app lam inputs SoundnessBetaAncestor.actualFlow rfl balance rfl transparency
    allPorts (fun route => selection.selected_route_walk initial matching allPorts route)
    (.nil _) actualRelative (.nil _)
    (.root (.atom 0) (.atom 1) (.var (.atom 2) 0) (.lam (.atom 3) (.var (.atom 4) 0)))
    rfl paths binders typedBinders
  exact ⟨beta,selection,result⟩

theorem actual_typed_target_variable :
    ∃ (beta : BetaEdge actualBetaSite.net)
      (selection : SourceEdgeSelection original actualBetaSite.net (.inl ())),∃ word,
      developed.sourceTrail selection.atomWord beta.principal beta.reverseRoute [.body]=some word ∧
      ∀ requested : Context,∃ output count,BetaDetourBlocks actualBetaSite.net word requested output count := by
  obtain ⟨beta,selection,paths⟩ := actual_typed_path_step
  obtain ⟨word,eval,assigned⟩ := paths (p:=[.body]) (sub:=.var (.atom 4) 0) rfl
  exact ⟨beta,selection,word,eval,assigned⟩
#print axioms actual_typed_path_step
#print axioms actual_typed_target_variable
#print axioms TypedSyntaxBinders.copied_lambda_step
#print axioms BetaDetourBlocks.detour_assignments
end Lamping.Checks.SoundnessFirstHistoryEvaluation
namespace Lamping.Checks.SoundnessFirstHistoryEvaluation
open AG Graph Lambda Lambda.Labelled
/-- A real fixed-fiber relative schedule consumes the full joint typed
history theorem. No intermediate Q or R is a fixture premise. -/
theorem actual_typed_joint_history :
    ∃ (beta : BetaEdge actualBetaSite.net)
      (selection : SourceEdgeSelection original actualBetaSite.net (.inl ())),
      GeneratedSyntaxPaths selection beta developed ∧SupportedSyntaxBinders selection beta developed ∧
      TypedSyntaxPaths selection beta developed ∧TypedSyntaxBinders selection beta developed := by
  have closed : Closed identityApp := by change (0<1) ∧ (0<1); decide
  have matching : Matches actualBetaSite.net (.inl ()) original.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨initialBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initialBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  obtain ⟨beta,_app,_lam,selection,joint⟩ := actualBetaSite.relative_history_typed
    (init_is_INIT identityApp) closed matching inputs SoundnessBetaAncestor.actualFlow rfl balance rfl transparency
  have labels : History [[]] original developed := .cons (.root _ _ _ _) (.nil _)
  exact ⟨beta,selection,joint actualRelative labels⟩

/-- Q supplies a true assignment for the copied target bound variable, and
R proves its shell at the SAME chosen target lambda occurrence and SAME
root input. The input may contain arbitrary nonempty marker subtrees. -/
theorem actual_typed_joint_binding (requested : Context) :
    ∃ (ambient loop : List (Endpoint actualBetaSite.net)) (binder : _)
      (output seam : Context) (count : Nat),
      BetaDetourBlocks actualBetaSite.net (ambient++loop) requested output count ∧
      ExpandedLabelling actualBetaSite.net ambient requested seam ∧
      Context.SameShell (actualBetaSite.net.label binder).index seam output := by
  obtain ⟨beta,selection,_generated,support,paths,binders⟩ := actual_typed_joint_history
  obtain ⟨ambient,loop,binder,ctx,ambientEval,leafEval,_support,shape,role,finish⟩ :=
    support (p:=[]) (stamp:=developed.label) (body:=.var (.atom 4) 0) (q:=[]) rfl rfl
  obtain ⟨output,count,whole⟩ := paths.at_word (p:=[.body]) (sub:=.var (.atom 4) 0) rfl leafEval requested
  have nonempty : ambient≠[] := by intro empty; rw [empty] at finish; cases finish
  obtain ⟨seam,before⟩ := (whole.labelling actualBetaSite.net).prefix nonempty
  have shell := binders (p:=[]) (stamp:=developed.label) (body:=.var (.atom 4) 0) (q:=[])
    rfl rfl ambientEval leafEval shape role finish whole before
  exact ⟨ambient,loop,binder,output,seam,count,whole,before,shell⟩

#print axioms actual_typed_joint_history
#print axioms actual_typed_joint_binding
#print axioms PathSite.relative_history_typed
#print axioms PathSite.relative_typed_binders_step
end Lamping.Checks.SoundnessFirstHistoryEvaluation
namespace Lamping.Checks.SoundnessFirstHistoryEvaluation
open AG Graph Lambda Lambda.Labelled
private def argumentAtoms : List (Endpoint actualBetaSite.net) :=
  [.inl ⟨.inr (.inl ()),.inr true⟩,.inr (.inr (.inl (.inr ()),true))]
private theorem argumentAtomsLabels (a : Context) : Labelling actualBetaSite.net argumentAtoms a a :=
  .cons (LabelledTurn.transparent (g:=actualBetaSite.net) (.inl (.inr ())) false a) (.single _ _)
private theorem argumentAtomsForward : Forward actualBetaSite.net argumentAtoms :=
  .transparent (.inl (.inr ())) false rfl rfl (.single _)
private def argumentAccess : RootAccess actualBetaSite.net (.inl ()) :=
  ⟨(.inr (.inl (.inl ())))::argumentAtoms,
   ⟨⟨⟨Context.empty,Context.empty,
      .cons (LabelledTurn.node (g:=actualBetaSite.net) (.inr (.inl ())) appCtx appArg (.direct (.appArg _)))
        (argumentAtomsLabels _)⟩,
      .node (.inr (.inl ())) appCtx appArg rfl rfl ⟨rfl,Or.inr rfl⟩ argumentAtomsForward⟩,
     rfl,⟨.lam,rfl⟩⟩⟩
/-- The actual original ARGUMENT edge is selected from source Matches and
locked to its physical occurrence. Its contraction constructs target labels
and the literal residual without being supplied a target shape. -/
theorem actual_atomic_source_fragment (a : Context) :
    ∃ (edge : BetaEdge actualBetaSite.net) (target : List (Endpoint actualBetaSite.reduce)),
      BetaPathResidual actualBetaSite edge (target.map (plugEnd _ _).invFun) argumentAtoms ∧
      Labelling actualBetaSite.reduce target a a ∧
      target.head?=some (AG.plugLeft _ _ (.inr (.inl (.inr (.inl true))))) ∧
      target.getLast?=some (actualBetaSite.reduce.wire (.inl ⟨.inl (.inr (.inl ())),.inl ()⟩)) := by
  have closed : Closed identityApp := by change (0<1) ∧ (0<1); decide
  have matching : Matches actualBetaSite.net (.inl ()) original.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  have source : SourceSubterm [] .external original [.arg] [] (.appArg (.atom 0))
      (.lam (.atom 3) (.var (.atom 4) 0)) := .arg .nil
  obtain ⟨fragment⟩ := matching.base_source_edge_fragment closed source
  have childWord : accessWord actualBetaSite.net argumentAccess.val=[.arg] := rfl
  have sameAccess : fragment.access=argumentAccess := matching.accessWord_injective (fragment.word.trans childWord.symm)
  have split := (fragment.child_prefix (term:=original) matching SourceDeparture.arg parent rfl).2
  have segmentEq : fragment.segments=argumentAtoms := by
    rw [sameAccess] at split
    exact (List.cons.inj split).2.symm
  have first : fragment.fromEndpoint=actualBetaSite.outsideEnd (.inr (.inl (.inr (.inl true)))) := by
    have start := fragment.start
    rw [segmentEq] at start
    exact (Option.some.inj start).symm
  obtain ⟨edge,_geometry⟩ := actualBetaSite.siteBetaGeometry_exists
  obtain ⟨target,residual,labels,head,ends⟩ := fragment.beta_atomic_contraction actualBetaSite edge
    (.inr (.inl (.inr (.inl true)))) first (by rw [segmentEq]; exact argumentAtomsLabels a)
  have finish : fragment.segments.getLast?=some
      (actualBetaSite.outsideEnd ((cutFragment actualBetaSite.net (pathPartition (Schema.beta 0) Unit) actualBetaSite.closed).wire
        (.inl ⟨.inr (.inl ()),.inl ()⟩))) := by rw [segmentEq]; rfl
  have targetFinish := ends _ finish
  have targetFinish' : target.getLast?=some (actualBetaSite.reduce.wire (.inl ⟨.inl (.inr (.inl ())),.inl ()⟩)) := by
    exact targetFinish.trans (congrArg some (plugLeft_wire _ _ _).symm)
  exact ⟨edge,target,by simpa only [segmentEq] using residual,labels,head,targetFinish'⟩

/-- The complete old app-to-argument visit emits a real syntax token, so it
cannot be silently treated as an atomic empty-word fragment. -/
theorem direct_argument_skip_is_not_atomic :
    accessWord actualBetaSite.net
      [.inr (.inl (.inl ())),.inl ⟨.inr (.inl ()),.inr true⟩]≠[] := by
  decide
#print axioms actual_atomic_source_fragment
#print axioms direct_argument_skip_is_not_atomic
#print axioms PathSite.beta_atomic_contraction
end Lamping.Checks.SoundnessFirstHistoryEvaluation
namespace Lamping.Checks.SoundnessFirstHistoryEvaluation
open AG Graph Lambda Lambda.Labelled
private theorem actual_port_eq {n m : BetaKept⊕(Unit⊕Unit)}
    {p : Port (actualBetaSite.net.label n).sort} {q : Port (actualBetaSite.net.label m).sort}
    (same : n=m) (role : HEq p q) :
    (.inl ⟨n,p⟩ : Endpoint actualBetaSite.net)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq role
  rfl
/-- The compound label on I I's developed ROOT lambda is interpreted by a
real shared syntax trail. Its complete source-route image, including the
actual beta bars, contracts to a genuinely labelled RHS root route with an
empty word, without giving the target path or its shape to the theorem. -/
theorem actual_compound_route_contraction (requested : Context) :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net))
      (target : List (Endpoint actualBetaSite.reduce)) (output : Context),
      BetaPathResidual actualBetaSite edge (target.map (plugEnd _ _).invFun) old ∧
      Labelling actualBetaSite.reduce target requested output ∧accessWord actualBetaSite.reduce target=[] := by
  have closed : Closed identityApp := by change (0<1) ∧ (0<1); decide
  have initial : INIT original := init_is_INIT identityApp
  have matching : Matches actualBetaSite.net (.inl ()) original.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨initialBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initialBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  obtain ⟨beta,app,lam,allPorts⟩ := actualBetaSite.selected_beta_source_ports initial matching
  let selection := matching.source_edge_selection closed
  have allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original)
      (SelectedDegree original (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase)) start stamp finish →
      ∃ walk : PhysicalSourceWalk original (.inl ()) beta start stamp finish,walk.edges=selection.evalLabel beta stamp :=
    fun route => selection.selected_route_walk initial matching allPorts route
  have geometry : SiteBetaGeometry actualBetaSite beta :=
    ⟨actual_port_eq app beta.appCtx_role,actual_port_eq lam beta.lamBody_role,
      actual_port_eq lam beta.lamBind_role,actual_port_eq app beta.appArg_role⟩
  have paths : TypedSyntaxPaths selection beta original := matching.typed_syntax_paths initial inputs selection beta
  have binders : SupportedSyntaxBinders selection beta original := matching.supported_syntax_binders initial selection beta
  have typedBinders : TypedSyntaxBinders selection beta original := matching.typed_syntax_binders initial transparency selection beta
  have typed : TypedSyntaxPaths selection beta developed := actualBetaSite.relative_typed_paths_step initial matching
    selection beta app lam inputs SoundnessBetaAncestor.actualFlow rfl balance rfl transparency allPorts allWalks
    (.nil _) actualRelative (.nil _)
    (.root (.atom 0) (.atom 1) (.var (.atom 2) 0) (.lam (.atom 3) (.var (.atom 4) 0)))
    rfl paths binders typedBinders
  have history : History [[]] original developed := .cons (.root _ _ _ _) (.nil _)
  have routes := relative_development_selected_routes initial actualRelative history
  obtain ⟨finish,trail,eval⟩ := selection.syntax_evaluation initial matching allWalks routes
    (p:=[]) (sub:=developed) rfl
  obtain ⟨output,count,blocks⟩ := typed.at_word (p:=[]) (sub:=developed) rfl eval requested
  have image : SourceRouteImage original (.inl ()) beta .external developed.label finish trail.edges := by
    cases image : trail.image with
    | lam route => exact route
  obtain ⟨raw,residual,labels,word⟩ := image.beta_contract_word actualBetaSite initial matching geometry
    (blocks.labelling _) (.inr (.inl (.inl (.inl ())))) trail.rooted
  let target := raw.map (plugEnd _ _)
  have actualResidual : BetaPathResidual actualBetaSite beta (target.map (plugEnd _ _).invFun) trail.edges := by
    have same : target.map (plugEnd _ _).invFun=raw := by
      simp only [target,List.map_map]
      simp only [Function.comp_def, (plugEnd _ _).left_inv]
      exact congrFun List.map_id_fun raw
    rw [same]
    exact residual
  exact ⟨beta,trail.edges,target,output,actualResidual,labels.actual _ _,word⟩

theorem actual_complete_syntax_contraction (requested : Context) (position : Path) (sub : LTerm)
    (lookup : developed.subterm position=some sub) :
    ∃ (edge : BetaEdge actualBetaSite.net) (old : List (Endpoint actualBetaSite.net))
      (target : List (Endpoint actualBetaSite.reduce)) (output : Context),
      BetaPathResidual actualBetaSite edge (target.map (plugEnd _ _).invFun) old ∧
      Labelling actualBetaSite.reduce target requested output ∧accessWord actualBetaSite.reduce target=position := by
  have closed : Closed identityApp := by change (0<1) ∧ (0<1); decide
  have initial : INIT original := init_is_INIT identityApp
  have matching : Matches actualBetaSite.net (.inl ()) original.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨initialBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initialBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  obtain ⟨beta,app,lam,allPorts⟩ := actualBetaSite.selected_beta_source_ports initial matching
  let selection := matching.source_edge_selection closed
  have allWalks : ∀ {start stamp finish},SelectedSourceRoute (sourceEdges [] .external original)
      (SelectedDegree original (actualBetaSite.betaSyntaxFiber (.inl ()) original.erase)) start stamp finish →
      ∃ walk : PhysicalSourceWalk original (.inl ()) beta start stamp finish,walk.edges=selection.evalLabel beta stamp :=
    fun route => selection.selected_route_walk initial matching allPorts route
  have geometry : SiteBetaGeometry actualBetaSite beta :=
    ⟨actual_port_eq app beta.appCtx_role,actual_port_eq lam beta.lamBody_role,
      actual_port_eq lam beta.lamBind_role,actual_port_eq app beta.appArg_role⟩
  have paths : TypedSyntaxPaths selection beta original := matching.typed_syntax_paths initial inputs selection beta
  have binders : SupportedSyntaxBinders selection beta original := matching.supported_syntax_binders initial selection beta
  have typedBinders : TypedSyntaxBinders selection beta original := matching.typed_syntax_binders initial transparency selection beta
  have typed : TypedSyntaxPaths selection beta developed := actualBetaSite.relative_typed_paths_step initial matching
    selection beta app lam inputs SoundnessBetaAncestor.actualFlow rfl balance rfl transparency allPorts allWalks
    (.nil _) actualRelative (.nil _)
    (.root (.atom 0) (.atom 1) (.var (.atom 2) 0) (.lam (.atom 3) (.var (.atom 4) 0)))
    rfl paths binders typedBinders
  have history : History [[]] original developed := .cons (.root _ _ _ _) (.nil _)
  have routes := relative_development_selected_routes initial actualRelative history
  obtain ⟨finish,trail,eval⟩ := selection.syntax_evaluation initial matching allWalks routes
    (p:=position) (sub:=sub) lookup
  obtain ⟨output,count,blocks⟩ := typed.at_word (p:=position) (sub:=sub) lookup eval requested
  obtain ⟨raw,residual,labels,word⟩ := trail.image.beta_contract_word actualBetaSite initial matching
    SoundnessBetaAncestor.actualFlow rfl actualRelative (by simp [Marked.Normal]) history geometry [] rfl
    (blocks.labelling _) (.inr (.inl (.inl (.inl ())))) trail.rooted
  let target := raw.map (plugEnd _ _)
  have actualResidual : BetaPathResidual actualBetaSite beta (target.map (plugEnd _ _).invFun) trail.edges := by
    have same : target.map (plugEnd _ _).invFun=raw := by
      simp only [target,List.map_map]
      simp only [Function.comp_def, (plugEnd _ _).left_inv]
      exact congrFun List.map_id_fun raw
    rw [same]
    exact residual
  exact ⟨beta,trail.edges,target,output,actualResidual,labels.actual _ _,word⟩

#print axioms actual_complete_syntax_contraction
#print axioms SyntaxTrailImage.beta_contract_word
theorem developed_root_label_is_not_atomic (n : Nat) : developed.label≠Labelled.Label.atom n := by
  intro impossible
  cases impossible
#print axioms actual_compound_route_contraction
#print axioms developed_root_label_is_not_atomic
#print axioms SourceRouteImage.beta_contract_word
end Lamping.Checks.SoundnessFirstHistoryEvaluation
namespace Lamping.Checks.SoundnessFirstHistoryEvaluation
open AG Graph Lambda Lambda.Labelled
/-- Real encoded I I and its actual complete fiber development consume the
entire canonical beta Matches theorem, with no intermediate target facts. -/
theorem actual_complete_beta_matches : Matches actualBetaSite.reduce (.inl ()) developed.erase := by
  have closed : Closed identityApp := by change (0<1) ∧(0<1); decide
  have initial : INIT original := init_is_INIT identityApp
  have matching : Matches actualBetaSite.net (.inl ()) original.erase :=
    betaEncodingIso.matches (encode_closed_matches identityApp closed 0)
  have inputs := betaEncodingIso.rootInputs (encode_closed_independence identityApp closed 0).rootInputs
  obtain ⟨initialBalance⟩ := encode_indexed_balance identityApp 0
  have balance := betaEncodingIso.indexed_balance initialBalance
  have transparency := betaEncodingIso.transparency (encode_closed_transparency identityApp closed 0)
  exact actualBetaSite.beta_complete_matches initial closed matching inputs SoundnessBetaAncestor.actualFlow rfl
    balance rfl transparency actualRelative (by simp [Marked.Normal]) (.cons (.root _ _ _ _) (.nil _))

/-- The resulting actual variable access carries the correct de Bruijn
observation, including suffix existence AND uniqueness. -/
theorem actual_complete_target_variable :
    ∃ access : RootAccess actualBetaSite.reduce (.inl ()),
      accessWord actualBetaSite.reduce access.val=[.body] ∧Observes actualBetaSite.reduce access.val (.var 0) := by
  obtain ⟨access,word,observes⟩ := Matches.observation actualBetaSite.reduce actual_complete_beta_matches
    (⟨[.body],by decide⟩ : Position developed.erase)
  obtain ⟨u,atU,observation⟩ := observes
  have actualLookup : subtermAt developed.erase [.body]=some (.var 0) := by decide
  have same := Option.some.inj (actualLookup.symm.trans atU)
  subst u
  exact ⟨access,word,observation⟩
#print axioms actual_complete_beta_matches
#print axioms actual_complete_target_variable
#print axioms PathSite.beta_complete_matches
#print axioms PathSite.beta_variable_access
#print axioms PathSite.relative_history_typed_with_walks
#print axioms PathSite.relative_history_typed
end Lamping.Checks.SoundnessFirstHistoryEvaluation

namespace Lamping.Checks.SoundnessIdentityNormal
open AG Graph Lambda
abbrev graph := (encode 0 identity).net
theorem actual_cro_level : graph.label (.inr ())=label .cro 0 := rfl
private theorem level_zero (node : (encode 0 identity).N) : (graph.label node).index=0 := by
  rcases node with a|b <;> rfl
private theorem no_active (node : (encode 0 identity).N) :
    (graph.label node).sort≠.op .app ∧(graph.label node).sort≠.op .fan ∧(graph.label node).sort≠.op .bra := by
  cases node with
  | inl u => cases u; change (Kind.op .lam≠.op .app) ∧(Kind.op .lam≠.op .fan) ∧(Kind.op .lam≠.op .bra); decide
  | inr u => cases u; change (Kind.op .cro≠.op .app) ∧(Kind.op .cro≠.op .fan) ∧(Kind.op .cro≠.op .bra); decide
private theorem labels_injective : Function.Injective graph.label := by
  intro a b same
  rcases a with a|a <;> rcases b with b|b
  · cases a; cases b; rfl
  · cases same
  · cases same
  · cases a; cases b; rfl

theorem normal : GraphNormal (ActualNet.initial identity) := by
  intro schema target step
  cases step with
  | atSite kept site before after =>
    let active := before.nodes.invFun (.inr (.inl ()))
    let passive := before.nodes.invFun (.inr (.inr ()))
    have activeLabel : graph.label active=label schema.active schema.low := before.symm.labels _
    have passiveLabel : graph.label passive=label schema.passive schema.high := before.symm.labels _
    have low : schema.low=0 := (congrArg Graph.Label.index activeLabel).symm.trans (level_zero active)
    have high : schema.high=0 := (congrArg Graph.Label.index passiveLabel).symm.trans (level_zero passive)
    have kinds := no_active active
    have distinct : active≠passive := by
      intro same
      have images := congrArg before.nodes same
      simp only [active,passive,before.nodes.right_inv] at images
      cases images
    cases schema with
    | beta i => exact kinds.1 (congrArg Graph.Label.sort activeLabel)
    | fanCancel i => exact kinds.2.1 (congrArg Graph.Label.sort activeLabel)
    | braCancel i => exact kinds.2.2 (congrArg Graph.Label.sort activeLabel)
    | croCancel i => exact distinct (labels_injective (activeLabel.trans passiveLabel.symm))
    | fanAction f i j lt => exact kinds.2.1 (congrArg Graph.Label.sort activeLabel)
    | braAction f i j lt => exact kinds.2.2 (congrArg Graph.Label.sort activeLabel)
    | croAction f i j lt => change i=0 at low; change j=0 at high; omega
/-- The actual graph-normal hypothesis is proved above, then the zero trace
consumes the genuine reachable-normal-form theorem without an NF oracle. -/
theorem actual_initial_normal_reflection :
    ∃ u,Betas identity u ∧Closed u ∧Matches graph (.inl ()) u ∧¬∃ v,Beta u v := by
  have closed : Closed identity := by change 0<1; decide
  exact initial_trace_normal_form identity closed (ActualNet.initial identity) [] (.refl _) normal
#print axioms actual_initial_normal_reflection
#print axioms actual_cro_level
#print axioms normal
end Lamping.Checks.SoundnessIdentityNormal