import Lamping.Lamping.BetaCompleteMatching
import Lamping.Lamping.InitialPatchRoutes
import Lamping.Lamping.BetaForwardCoverageMatching
import Lamping.Lamping.FlowRootPaths
import Lamping.Lamping.HighTailTransport
import Lamping.Lamping.ControlConstructorTransport
import Lamping.Lamping.PathShellReflection

namespace Lamping.Checks.UnpairedSourceProfiles
open AG Graph

/-- Two real context-to-argument primitives. Their geometry raises the
height from 0 through 1 to 2, while their contexts remain unchanged. -/
def HeadProgram (a b : Context) : Prop :=
  ∃ middle,Traversal 0 (.op .app) appCtx appArg a middle ∧
    Traversal 1 (.op .app) appCtx appArg middle b

theorem head_program (a : Context) : HeadProgram a a :=
  ⟨a,.direct (.appArg a),.direct (.appArg a)⟩

private theorem app_argument_identity {level a b}
    (rule : Traversal level (.op .app) appCtx appArg a b) : a=b := by
  cases rule with
  | direct passage => cases passage; rfl
  | inverse passage => cases passage

theorem head_identity {a b} (path : HeadProgram a b) : a=b := by
  obtain ⟨middle,left,right⟩ := path
  exact (app_argument_identity left).trans (app_argument_identity right)

/-- The complete two clauses of old I for this head, with source lamBody0
and target lamBind1 (hence terminal width 2). No claim about the whole net
is made by this local program profile. -/
theorem head_independence_profile (a : Context) :
    (∀ replacement,∃ output,HeadProgram (a.replace 0 replacement) output) ∧
    ∃ width,0≤width ∧
      (∀ c,a=a.replace 2 c →a=a.replace width c) ∧
      (∀ c,HeadProgram (a.replace width c) (a.replace 2 c)) := by
  exact ⟨fun replacement => ⟨_,head_program _⟩,2,by omega,fun _ fixed => fixed,fun _ => head_program _⟩

def markerInput : Context := Context.empty.cons (.o .empty)

theorem reference_reader : Traversal 0 (.op .fan) (.inl ()) fanO markerInput Context.empty := by
  simpa [markerInput] using Traversal.inverse (Passage.fanO (i:=0) Context.empty Context.empty .empty)

theorem reader_input_total (replacement : Context) :
    ∃ output,Traversal 0 (.op .fan) (.inl ()) fanO (markerInput.replace 1 replacement) output := by
  exact reference_reader.control_inverse_transfer (Or.inl rfl) _ (Context.replace_low _ _ (by decide : 0<1))

private theorem fixed_tail_transfer {a b : Context} {width terminal : Nat}
    (tails : a.tail width=b.tail terminal) (c : Context) (fixed : b=b.replace terminal c) :
    a=a.replace width c := by
  have same : c=b.tail terminal := by
    ext k
    have atLevel := congrArg (fun x : Context => x.get (terminal+k)) fixed
    simpa [Context.replace,Context.tail] using atLevel.symm
  rw [same,←tails,Context.replace_tail]

/-- A fan reader at base-height 2 is below its actual source appArg1.
It really satisfies the input clause at replace1, the strict width bound,
the fixed-tail clause and synchronized output at terminal width 2. -/
theorem reader_independence_profile :
    (∀ replacement,∃ output,Traversal 0 (.op .fan) (.inl ()) fanO (markerInput.replace 1 replacement) output) ∧
    ∃ width,1<width ∧
      (∀ c,Context.empty=Context.empty.replace 2 c →markerInput=markerInput.replace width c) ∧
      (∀ c,Traversal 0 (.op .fan) (.inl ()) fanO
        (markerInput.replace width c) (Context.empty.replace 2 c)) := by
  obtain ⟨loss,tails,sync⟩ := reference_reader.high_tail_sync 2 2 2 (by change (0 : Int)<2; decide) rfl rfl True.intro 0
  simp only [Nat.add_zero] at tails sync
  exact ⟨reader_input_total,2+loss,by omega,fixed_tail_transfer tails,sync⟩

/-- These two correctly indexed local I profiles do not by themselves
justify the new reverse-beta seam. This is not yet a whole-graph example. -/
theorem seam_replacement_fails : ¬∃ middle output,
    HeadProgram (markerInput.replace 0 Context.empty) middle ∧
      Traversal 0 (.op .fan) (.inl ()) fanO middle output := by
  rintro ⟨middle,output,head,reader⟩
  have same := head_identity head
  rw [Context.replace_zero] at same
  rw [←same] at reader
  have marker := reader.fan_marker
  simp [FanEdgeMarker,AG.fanO] at marker

#print axioms head_independence_profile
#print axioms reader_independence_profile
#print axioms seam_replacement_fails
end Lamping.Checks.UnpairedSourceProfiles

namespace Lamping.Checks.UnpairedSourceProfiles.Model
open AG Graph
inductive Kept where
  | rootLam | rootCro | badLam | appZero | appOne | reader | endLam
  | g0 | g1 | g2 | g3 | g4 | g5 | g6 | g7 | g8
  deriving DecidableEq, Repr
instance : FiniteNames Kept := ⟨[.rootLam,.rootCro,.badLam,.appZero,.appOne,.reader,.endLam,
  .g0,.g1,.g2,.g3,.g4,.g5,.g6,.g7,.g8],by intro k; cases k <;> simp⟩
def labels : Kept → Label signature
  | .rootLam | .badLam => label .lam 0
  | .rootCro => label .cro 0
  | .appZero => label .app 0
  | .appOne => label .app 1
  | .reader => label .fan 0
  | .endLam => label .lam 2
  | _ => garbage
abbrev End := Graph.End signature (Kept⊕(Unit⊕Unit)) Unit (Empty⊕Empty) (ambientLabel (.beta 1) labels)
def kp (k : Kept) (p : Port (labels k).sort) : End := .inl ⟨.inl k,p⟩
def ac (p : Port (.op .app)) : End := .inl ⟨.inr (.inl ()),p⟩
def la (p : Port (.op .lam)) : End := .inl ⟨.inr (.inr ()),p⟩
def wire : End → End
  | .inl ⟨.inl .rootLam,.inl _⟩ => .inr (.inl ())
  | .inl ⟨.inl .rootLam,.inr false⟩ => kp .rootCro (.inl ())
  | .inl ⟨.inl .rootLam,.inr true⟩ => kp .rootCro (.inr ())
  | .inl ⟨.inl .rootCro,.inl _⟩ => kp .rootLam lamBind
  | .inl ⟨.inl .rootCro,.inr _⟩ => kp .rootLam lamBody
  | .inl ⟨.inl .badLam,.inl _⟩ => kp .g0 ()
  | .inl ⟨.inl .badLam,.inr false⟩ => kp .g1 ()
  | .inl ⟨.inl .badLam,.inr true⟩ => kp .appZero appCtx
  | .inl ⟨.inl .appZero,.inl _⟩ => kp .g2 ()
  | .inl ⟨.inl .appZero,.inr false⟩ => kp .badLam lamBody
  | .inl ⟨.inl .appZero,.inr true⟩ => kp .appOne appCtx
  | .inl ⟨.inl .appOne,.inl _⟩ => kp .g3 ()
  | .inl ⟨.inl .appOne,.inr false⟩ => kp .appZero appArg
  | .inl ⟨.inl .appOne,.inr true⟩ => la lamBind
  | .inl ⟨.inl .reader,.inl _⟩ => ac appArg
  | .inl ⟨.inl .reader,.inr false⟩ => kp .endLam (.inl ())
  | .inl ⟨.inl .reader,.inr true⟩ => kp .g4 ()
  | .inl ⟨.inl .endLam,.inl _⟩ => kp .reader fanO
  | .inl ⟨.inl .endLam,.inr false⟩ => kp .g6 ()
  | .inl ⟨.inl .endLam,.inr true⟩ => kp .g5 ()
  | .inl ⟨.inl .g0,_⟩ => kp .badLam (.inl ())
  | .inl ⟨.inl .g1,_⟩ => kp .badLam lamBind
  | .inl ⟨.inl .g2,_⟩ => kp .appZero (.inl ())
  | .inl ⟨.inl .g3,_⟩ => kp .appOne (.inl ())
  | .inl ⟨.inl .g4,_⟩ => kp .reader fanStar
  | .inl ⟨.inl .g5,_⟩ => kp .endLam lamBody
  | .inl ⟨.inl .g6,_⟩ => kp .endLam lamBind
  | .inl ⟨.inl .g7,_⟩ => ac appCtx
  | .inl ⟨.inl .g8,_⟩ => la lamBody
  | .inl ⟨.inr (.inl _),.inl _⟩ => la (.inl ())
  | .inl ⟨.inr (.inl _),.inr false⟩ => kp .g7 ()
  | .inl ⟨.inr (.inl _),.inr true⟩ => kp .reader (.inl ())
  | .inl ⟨.inr (.inr _),.inl _⟩ => ac (.inl ())
  | .inl ⟨.inr (.inr _),.inr false⟩ => kp .appOne appArg
  | .inl ⟨.inr (.inr _),.inr true⟩ => kp .g8 ()
  | .inr (.inl _) => kp .rootLam (.inl ())
  | .inr (.inr ⟨e,_⟩) => nomatch e
private theorem wire_involutive (e : End) : wire (wire e)=e := by
  rcases e with ⟨node,p⟩ | (b|⟨e,d⟩)
  · rcases node with node | (u|u)
    · cases node <;> cases p <;> first | rfl | (rename_i q; cases q <;> rfl)
    · cases u; cases p <;> (rename_i q; cases q <;> rfl)
    · cases u; cases p <;> (rename_i q; cases q <;> rfl)
  · cases b; rfl
  · exact nomatch e
private theorem wire_distinct (e : End) : wire e≠e := by
  rcases e with ⟨node,p⟩ | (b|⟨e,d⟩)
  · rcases node with node | (u|u)
    · cases node <;> cases p <;> first | (intro h; cases h) | (rename_i q; cases q <;> intro h <;> cases h)
    · cases u; cases p <;> (rename_i q; cases q <;> intro h <;> cases h)
    · cases u; cases p <;> (rename_i q; cases q <;> intro h <;> cases h)
  · intro h; cases h
  · exact nomatch e
def pairing : Pairing End := ⟨wire,wire_involutive,wire_distinct⟩
def internal : Pairing (Bool⊕(Empty×Bool)) where
  mate | .inl b => .inl (!b) | .inr ⟨e,_⟩ => nomatch e
  involutive := by rintro (b|⟨e,d⟩); cases b <;> rfl; exact nomatch e
  fixedPointFree := by rintro (b|⟨e,d⟩); cases b <;> intro h <;> cases h; exact nomatch e
def site : PathSite (.beta 1) labels (B:=Unit) (W:=Empty) (V:=Empty) where
  wire := pairing
  internal := internal
  connected := by rintro (b|⟨e,d⟩); cases b; exact .refl _; exact .segment _; exact nomatch e
  wiring := by rintro (b|⟨e,d⟩); cases b <;> rfl; exact nomatch e
def nodeFlow : Kept⊕(Unit⊕Unit) → Bool
  | .inl .rootCro => true
  | .inl .g0 | .inl .g1 | .inl .g6 | .inl .g7 => true
  | _ => false

def flow : FlowBalance site.net (fun _ => true) where
  nodes := nodeFlow
  vertices := fun e => nomatch e
  wiring := by
    rintro (⟨node,p⟩ |(b|⟨e,d⟩))
    · rcases node with node |(u|u)
      · cases node <;> cases p <;> first | rfl | (rename_i q; cases q <;> rfl)
      · cases u; cases p <;> (rename_i q; cases q <;> rfl)
      · cases u; cases p <;> (rename_i q; cases q <;> rfl)
    · cases b; rfl
    · exact nomatch e

def nodeHeight : Kept⊕(Unit⊕Unit) → Int
  | .inl .reader | .inl .g4 | .inl .g5 => 2
  | .inl .g6 => 3
  | .inl .g1 | .inl .g3 | .inl .g7 | .inl .g8 => 1
  | _ => 0

def indexed : IndexedLevelBalance site.net (fun _ => 0) where
  nodes := nodeHeight
  vertices := fun e => nomatch e
  wiring := by
    rintro (⟨node,p⟩ |(b|⟨e,d⟩))
    · rcases node with node |(u|u)
      · cases node <;> cases p <;> first | rfl | (rename_i q; cases q <;> rfl)
      · cases u; cases p <;> (rename_i q; cases q <;> rfl)
      · cases u; cases p <;> (rename_i q; cases q <;> rfl)
    · cases b; rfl
    · exact nomatch e
  bounded := by
    rintro (node |(u|u))
    · change ControlIndexBound (labels node) (nodeHeight (.inl node))
      cases node <;> unfold ControlIndexBound <;> dsimp only [labels,nodeHeight,label,garbage] <;> decide
    · cases u; trivial
    · cases u; trivial

def oldHead : List (Endpoint site.net) := [kp .badLam lamBody,kp .appZero appArg,kp .appOne appArg]
def oldTail : List (Endpoint site.net) := [ac appArg,kp .reader fanO]

theorem old_head_labels (a : Context) : Labelling site.net oldHead a a :=
  .cons (LabelledTurn.node (g:=site.net) (.inl .appZero) appCtx appArg (.direct (.appArg a)))
    (.cons (LabelledTurn.node (g:=site.net) (.inl .appOne) appCtx appArg (.direct (.appArg a))) (.single _ _))
theorem old_tail_labels : Labelling site.net oldTail markerInput Context.empty :=
  .cons (LabelledTurn.node (g:=site.net) (.inl .reader) (.inl ()) fanO reference_reader) (.single _ _)

abbrev newEnd := Endpoint site.reduce
def newPath : List newEnd :=
  [.inl ⟨.inl .badLam,lamBody⟩,.inl ⟨.inl .appZero,appArg⟩,.inl ⟨.inl .appOne,appArg⟩,
   .inr (.inr (.inr (.inr false),true)),.inr (.inr (.inr (.inl true),false)),.inl ⟨.inl .reader,fanO⟩]

theorem new_labels : Labelling site.reduce newPath markerInput Context.empty :=
  .cons (LabelledTurn.node (g:=site.reduce) (.inl .appZero) appCtx appArg (.direct (.appArg _)))
    (.cons (LabelledTurn.node (g:=site.reduce) (.inl .appOne) appCtx appArg (.direct (.appArg _)))
      (.cons (LabelledTurn.transparent (g:=site.reduce) (.inr (.inr false)) false _)
        (.cons (LabelledTurn.transparent (g:=site.reduce) (.inr (.inl true)) true _)
          (.cons (LabelledTurn.node (g:=site.reduce) (.inl .reader) (.inl ()) fanO reference_reader) (.single _ _)))))

#print axioms old_head_labels
#print axioms old_tail_labels
#print axioms new_labels
def newStem : List newEnd :=
  [.inl ⟨.inl .badLam,lamBody⟩,.inl ⟨.inl .appZero,appArg⟩,.inl ⟨.inl .appOne,appArg⟩,
   .inr (.inr (.inr (.inr false),true))]
def newExit : newEnd := .inr (.inr (.inr (.inl true),false))
def newReader : newEnd := .inl ⟨.inl .reader,fanO⟩

theorem prefix_labels (a : Context) : Labelling site.reduce (newStem++[newExit]) a a :=
  .cons (LabelledTurn.node (g:=site.reduce) (.inl .appZero) appCtx appArg (.direct (.appArg a)))
    (.cons (LabelledTurn.node (g:=site.reduce) (.inl .appOne) appCtx appArg (.direct (.appArg a)))
      (.cons (LabelledTurn.transparent (g:=site.reduce) (.inr (.inr false)) false a)
        (.cons (LabelledTurn.transparent (g:=site.reduce) (.inr (.inl true)) true a) (.single _ _))))

theorem changed_input_rejected (output : Context) : ¬Labelling site.reduce newPath Context.empty output := by
  intro whole
  change Labelling site.reduce (newStem++newExit::[newReader]) Context.empty output at whole
  obtain ⟨middle,before,after⟩ := whole.split_segment
  have same := before.output_unique (prefix_labels Context.empty)
  rw [same] at after
  cases after with
  | cons turn tail =>
    change LabelledTurn site.reduce (.inl ⟨.inl .reader,.inl ()⟩) (.inl ⟨.inl .reader,fanO⟩) Context.empty _ at turn
    cases turn with
    | node _ _ _ rule =>
      change Traversal 0 (.op .fan) (.inl ()) fanO Context.empty _ at rule
      have marker := rule.fan_marker
      simp [FanEdgeMarker,AG.fanO] at marker

theorem target_not_independent : ¬Independence site.reduce () := by
  intro independent
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have fw : Forward site.reduce newPath := new_labels.forward_of_flow newFlow (by
    intro e head
    have same : (.inl ⟨.inl .badLam,lamBody⟩ : newEnd)=e := Option.some.inj head
    rw [←same]
    rfl)
  obtain ⟨changed,labels⟩ := (independent newPath (.inl ⟨.inl .badLam,lamBody⟩)
    (.inl ⟨.inl .endLam,.inl ()⟩) .lamBody .lamCtx 0 2 markerInput Context.empty rfl rfl
    (AtProperRole.lamBody (g:=site.reduce) (root:=()) (.inl .badLam) lamBody 0 rfl HEq.rfl) True.intro
    (AtProperRole.lamCtx (g:=site.reduce) (root:=()) (.inl .endLam) (Sum.inl ()) 2 rfl HEq.rfl) True.intro fw new_labels).1 Context.empty
  exact changed_input_rejected changed (by simpa only [Context.replace_zero] using labels)
#print axioms target_not_independent
end Lamping.Checks.UnpairedSourceProfiles.Model
namespace Lamping.Checks.UnpairedRootProof
open AG Graph Lambda UnpairedSourceProfiles UnpairedSourceProfiles.Model
abbrev rootEnd : Endpoint site.net := .inr (.inl ())
abbrev bodyEnd : Endpoint site.net := kp .rootLam lamBody
abbrev croEnd : Endpoint site.net := kp .rootCro (.inl ())
abbrev varPath : List (Endpoint site.net) := [rootEnd,bodyEnd,croEnd]

theorem root_labelling_cases {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (first : es.head?=some rootEnd) :
    es=[rootEnd] ∨ es=[rootEnd,bodyEnd] ∨ es=varPath := by
  obtain ⟨tail,same⟩ := List.head?_eq_some_iff.mp first
  subst es
  cases tail with
  | nil => exact .inl rfl
  | cons next tail =>
    cases labels with
    | cons turn rest =>
      obtain ⟨q,atQ,rule⟩ := turn.from_node (g:=site.net) (.inl .rootLam) (.inl ()) rfl
      have typed : Traversal 0 (.op .lam) (.inl ()) q _ _ := rule
      obtain ⟨port,_contexts⟩ := typed.lam_context
      subst q
      change next=bodyEnd at atQ
      subst next
      cases tail with
      | nil => exact .inr (.inl rfl)
      | cons next tail =>
        cases rest with
        | cons turn rest =>
          obtain ⟨q,atQ,rule⟩ := turn.from_node (g:=site.net) (.inl .rootCro) (.inr ()) rfl
          have port : q=Sum.inl () := by
            cases q with
            | inl u => cases u; rfl
            | inr u => cases u; exact False.elim (rule.distinct rfl)
          subst q
          change next=croEnd at atQ
          subst next
          cases tail with
          | nil => exact .inr (.inr rfl)
          | cons next tail =>
            cases rest with
            | cons turn _rest =>
              obtain ⟨q,_atQ,rule⟩ := turn.from_node (g:=site.net) (.inl .rootLam) lamBind rfl
              exact False.elim (rule.no_binding.1 rfl)


def loopPath : List (Endpoint site.net) := [bodyEnd,croEnd]
theorem loop_labels (a : Context) : Labelling site.net loopPath a (a.cons .empty) := by
  apply Labelling.cons _ (.single _ _)
  apply LabelledTurn.node (g:=site.net) (.inl .rootCro) (.inr ()) (.inl ())
  simpa only [Context.replace_zero] using Traversal.direct (Passage.cro (i:=0) a a)
theorem var_labels (a : Context) : Labelling site.net varPath a (a.cons .empty) :=
  .cons (.node (g:=site.net) (.inl .rootLam) (.inl ()) lamBody (.direct (.lamBody a))) (loop_labels a)
theorem body_prefix_labels (a : Context) : Labelling site.net [rootEnd,bodyEnd] a a :=
  .cons (.node (g:=site.net) (.inl .rootLam) (.inl ()) lamBody (.direct (.lamBody a))) (.single _ _)

theorem root_inputs : RootInputs site.net () := by
  intro es a b terminal role level labels _fw first _finish _at _incoming requested
  rcases root_labelling_cases labels first with same|same|same
  · subst es; exact ⟨requested,.single _ _⟩
  · subst es; exact ⟨requested,body_prefix_labels requested⟩
  · subst es; exact ⟨requested.cons .empty,var_labels requested⟩

private theorem binding_kind {kind : Kind} {bind : Port kind} (sort : kind=.op .lam)
    (role : HEq bind lamBind) : portKind kind bind=some .var := by
  subst kind
  cases eq_of_heq role
  rfl

def actual_loop (a : Context) : BindingLoop site.net loopPath a (a.cons .empty) where
  binder := .inl .rootLam
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := loop_labels a
  forward := (loop_labels a).forward_of_flow flow (by intro e first; cases Option.some.inj first; rfl)
  shell := by intro k bound; change k<0 at bound; omega

theorem root_transparency : Transparency site.net () := by
  intro es a b node ctx body bind sort ctxRole bodyRole bindRole first finish _fw labels
  have kind : accessKind site.net es=some .var := by
    rw [accessKind,finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact binding_kind sort bindRole
  rcases root_labelling_cases labels first with same|same|same
  · subst es; cases kind
  · subst es; cases kind
  · subst es
    have ends := congrArg site.net.wire.mate (Option.some.inj finish)
    have physical : (.inl ⟨node,bind⟩ : Endpoint site.net)=kp .rootLam lamBind := by
      simpa only [varPath,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.getD_some,
        Pairing.involutive] using ends.symm
    have nodes : node=Sum.inl Kept.rootLam := congrArg Sigma.fst (Sum.inl.inj physical)
    subst node
    have ctxEq : ctx=Sum.inl () := eq_of_heq ctxRole
    subst ctx
    have output : b=a.cons .empty := labels.output_unique (var_labels a)
    subst b
    exact ⟨[rootEnd],loopPath,a,actual_loop a,rfl,rfl,rfl,.single _ _⟩

abbrev identity : Term := .lam (.var 0)
def rootAccess : RootAccess site.net () :=
  ⟨[rootEnd],⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,.lam,rfl⟩⟩
def variableAccess : RootAccess site.net () :=
  ⟨varPath,⟨⟨⟨Context.empty,Context.empty.cons .empty,var_labels _⟩,
    (var_labels Context.empty).root_forward_of_flow flow () rfl rfl⟩,rfl,.var,rfl⟩⟩
theorem variable_suffix : BindingSuffix site.net variableAccess.val 0 :=
  ⟨[rootEnd],loopPath,Context.empty,Context.empty,Context.empty.cons .empty,
    actual_loop _,Sum.inl (),rfl,HEq.rfl,rfl,.single _ _,rfl⟩

theorem root_matches : Matches site.net () identity := by
  apply root_inputs.matches_of_kind_binding_coverage (indexed.nesting () rfl) root_transparency
  intro position
  have shapes : position.val=[] ∨ position.val=[.body] := by
    rcases position with ⟨p,valid⟩
    cases p with
    | nil => exact .inl rfl
    | cons step rest =>
      cases step with
      | fn | arg => simp [subtermAt] at valid
      | body =>
        cases rest with
        | nil => exact .inr rfl
        | cons step rest => cases step <;> simp [subtermAt] at valid
  rcases shapes with same|same
  · exact ⟨rootAccess,identity,(by rw [same]; rfl),(by rw [same]; rfl),rfl,True.intro⟩
  · exact ⟨variableAccess,.var 0,(by rw [same]; rfl),(by rw [same]; rfl),rfl,variable_suffix⟩

#print axioms root_labelling_cases
#print axioms root_inputs
#print axioms root_transparency
#print axioms root_matches
end Lamping.Checks.UnpairedRootProof

namespace Lamping.Checks.UnpairedSourceProfiles.Model
open AG Graph
private theorem node_turn {node : Kept⊕(Unit⊕Unit)} {p : Port (site.net.label node).sort} {f a b}
    (turn : LabelledTurn site.net (.inl ⟨node,p⟩) f a b) :
    ∃ q,f=.inl ⟨node,q⟩ ∧Traversal (site.net.label node).index (site.net.label node).sort p q a b := by
  cases turn with
  | node _ _ _ rule => exact ⟨_,rfl,rule⟩
private theorem bind_no_turn {f a b} (turn : LabelledTurn site.net (la lamBind) f a b) : False := by
  obtain ⟨q,_fEq,rule⟩ := node_turn turn
  exact rule.not_binding_heq rfl HEq.rfl
private theorem selected_lambda_turn {f a b} (turn : LabelledTurn site.net (la (.inl ())) f a b) :
    f=la lamBody ∧a=b := by
  obtain ⟨q,fEq,rule⟩ := node_turn turn
  have typed : Traversal 1 (.op .lam) (.inl ()) q a b := rule
  obtain ⟨port,contexts⟩ := typed.lam_context
  subst q
  exact ⟨fEq,contexts⟩
private theorem end_lambda_turn {f a b} (turn : LabelledTurn site.net (kp .endLam (.inl ())) f a b) :
    f=kp .endLam lamBody ∧a=b := by
  obtain ⟨q,fEq,rule⟩ := node_turn turn
  have typed : Traversal 2 (.op .lam) (.inl ()) q a b := rule
  obtain ⟨port,contexts⟩ := typed.lam_context
  subst q
  exact ⟨fEq,contexts⟩
private theorem app_zero_turn {f a b} (turn : LabelledTurn site.net (kp .appZero appCtx) f a b) :
    (f=kp .appZero (.inl ()) ∨f=kp .appZero appArg) ∧a=b := by
  obtain ⟨q,fEq,rule⟩ := node_turn turn
  have typed : Traversal 0 (.op .app) appCtx q a b := rule
  have contexts : a=b := typed.proper_context
  cases q with
  | inl u => cases u; exact ⟨Or.inl fEq,contexts⟩
  | inr branch => cases branch with
    | false => exact False.elim (typed.distinct rfl)
    | true => exact ⟨Or.inr fEq,contexts⟩
private theorem app_one_turn {f a b} (turn : LabelledTurn site.net (kp .appOne appCtx) f a b) :
    (f=kp .appOne (.inl ()) ∨f=kp .appOne appArg) ∧a=b := by
  obtain ⟨q,fEq,rule⟩ := node_turn turn
  have typed : Traversal 1 (.op .app) appCtx q a b := rule
  have contexts : a=b := typed.proper_context
  cases q with
  | inl u => cases u; exact ⟨Or.inl fEq,contexts⟩
  | inr branch => cases branch with
    | false => exact False.elim (typed.distinct rfl)
    | true => exact ⟨Or.inr fEq,contexts⟩
private theorem reader_turn {f a b} (turn : LabelledTurn site.net (kp .reader (.inl ())) f a b) :
    (f=kp .reader fanO ∧Traversal 0 (.op .fan) (.inl ()) fanO a b) ∨
    (f=kp .reader fanStar ∧Traversal 0 (.op .fan) (.inl ()) fanStar a b) := by
  obtain ⟨q,fEq,rule⟩ := node_turn turn
  have typed : Traversal 0 (.op .fan) (.inl ()) q a b := rule
  cases q with
  | inl u => cases u; exact False.elim (typed.distinct rfl)
  | inr branch => cases branch with
    | false => exact Or.inl ⟨fEq,typed⟩
    | true => exact Or.inr ⟨fEq,typed⟩

private def Typed (es : List (Endpoint site.net)) : Prop := ∃ kind,accessKind site.net es=some kind
private theorem typed_tail {e f es} (typed : Typed (e::f::es)) : Typed (f::es) := by
  obtain ⟨kind,observed⟩ := typed
  exact ⟨kind,by simpa only [accessKind,List.getLast?_cons_cons] using observed⟩
private theorem no_garbage_rule {index kind p q a b} (rule : Traversal index kind p q a b)
    (sort : kind=.garbage) : False := by
  cases rule with
  | direct passage => cases passage <;> cases sort
  | inverse passage => cases passage <;> cases sort
private theorem no_garbage_turn {node : Kept⊕(Unit⊕Unit)} {port : Port (site.net.label node).sort} {f a b}
    (turn : LabelledTurn site.net (.inl ⟨node,port⟩) f a b) (sort : (site.net.label node).sort=.garbage) : False := by
  obtain ⟨q,_fEq,rule⟩ := node_turn turn
  exact no_garbage_rule rule sort
private theorem no_garbage_kind {kind} {p : Port kind} (sort : kind=.garbage) : portKind kind p=none := by
  subst kind; rfl
private theorem garbage_head {e tail a b} (labelling : Labelling site.net (e::tail) a b)
    (typed : Typed (e::tail)) {node : Kept⊕(Unit⊕Unit)} {port : Port (site.net.label node).sort}
    (wireEq : site.net.wire e=.inl ⟨node,port⟩) (sort : (site.net.label node).sort=.garbage) : False := by
  cases labelling with
  | single =>
    obtain ⟨kind,observed⟩ := typed
    simp only [accessKind,List.getLast?_singleton,Option.bind_some] at observed
    rw [wireEq] at observed
    change portKind (site.net.label node).sort port=some kind at observed
    rw [no_garbage_kind sort] at observed
    cases observed
  | cons turn tail => rw [wireEq] at turn; exact no_garbage_turn turn sort
private theorem binding_stop {tail a b} (labelling : Labelling site.net (kp .appOne appArg::tail) a b) :
    tail=[] ∧a=b := by
  cases labelling with
  | single => exact ⟨rfl,rfl⟩
  | cons turn rest => exact False.elim (bind_no_turn turn)
private theorem end_context_stop {tail a b} (labelling : Labelling site.net (kp .reader fanO::tail) a b)
    (typed : Typed (kp .reader fanO::tail)) : tail=[] ∧a=b := by
  cases labelling with
  | single => exact ⟨rfl,rfl⟩
  | cons turn rest =>
    have restTyped := typed_tail typed
    obtain ⟨rfl,_contexts⟩ := end_lambda_turn turn
    exact False.elim (garbage_head rest restTyped rfl rfl)
private theorem selected_context_stop {tail a b} (labelling : Labelling site.net (ac (.inl ())::tail) a b)
    (typed : Typed (ac (.inl ())::tail)) : tail=[] ∧a=b := by
  cases labelling with
  | single => exact ⟨rfl,rfl⟩
  | cons turn rest =>
    have restTyped := typed_tail typed
    obtain ⟨rfl,_contexts⟩ := selected_lambda_turn turn
    exact False.elim (garbage_head rest restTyped rfl rfl)
private theorem reader_shape {tail a b} (labelling : Labelling site.net (ac appArg::tail) a b)
    (typed : Typed (ac appArg::tail)) : tail=[kp .reader fanO] ∧Traversal 0 (.op .fan) (.inl ()) fanO a b := by
  cases labelling with
  | single => obtain ⟨kind,observed⟩ := typed; change none=some kind at observed; cases observed
  | cons turn rest =>
    have restTyped := typed_tail typed
    rcases reader_turn turn with ⟨rfl,rule⟩|⟨rfl,rule⟩
    · obtain ⟨rfl,contexts⟩ := end_context_stop rest restTyped
      exact ⟨rfl,by rw [←contexts]; exact rule⟩
    · exact False.elim (garbage_head rest restTyped rfl rfl)
private theorem app_one_shape {tail a b} (labelling : Labelling site.net (kp .appZero appArg::tail) a b)
    (typed : Typed (kp .appZero appArg::tail)) :
    (tail=[] ∨tail=[kp .appOne appArg]) ∧a=b := by
  cases labelling with
  | single => exact ⟨Or.inl rfl,rfl⟩
  | cons turn rest =>
    have restTyped := typed_tail typed
    obtain ⟨shape,contexts⟩ := app_one_turn turn
    rcases shape with rfl|rfl
    · exact False.elim (garbage_head rest restTyped rfl rfl)
    · obtain ⟨rfl,after⟩ := binding_stop rest
      exact ⟨Or.inr rfl,contexts.trans after⟩
private theorem app_zero_shape {tail a b} (labelling : Labelling site.net (kp .badLam lamBody::tail) a b)
    (typed : Typed (kp .badLam lamBody::tail)) :
    (tail=[] ∨tail=[kp .appZero appArg] ∨tail=[kp .appZero appArg,kp .appOne appArg]) ∧a=b := by
  cases labelling with
  | single => exact ⟨Or.inl rfl,rfl⟩
  | cons turn rest =>
    have restTyped := typed_tail typed
    obtain ⟨shape,contexts⟩ := app_zero_turn turn
    rcases shape with rfl|rfl
    · exact False.elim (garbage_head rest restTyped rfl rfl)
    · obtain ⟨shape,after⟩ := app_one_shape rest restTyped
      rcases shape with rfl|rfl
      · exact ⟨Or.inr (Or.inl rfl),contexts.trans after⟩
      · exact ⟨Or.inr (Or.inr rfl),contexts.trans after⟩
private def Total (es : List (Endpoint site.net)) : Prop := ∀ input,∃ output,Labelling site.net es input output
private theorem singleton_total (e : Endpoint site.net) : Total [e] := fun a => ⟨a,.single _ _⟩
private theorem bad_body_total {tail a b} (labelling : Labelling site.net (kp .badLam lamBody::tail) a b)
    (typed : Typed (kp .badLam lamBody::tail)) : Total (kp .badLam lamBody::tail) := by
  obtain ⟨shape,_contexts⟩ := app_zero_shape labelling typed
  rcases shape with rfl|rfl|rfl
  · exact singleton_total _
  · intro input
    exact ⟨input,.cons (.node (g:=site.net) (.inl .appZero) appCtx appArg (.direct (.appArg input))) (.single _ _)⟩
  · exact fun input => ⟨input,old_head_labels input⟩
private theorem dummy_zero_argument_total {tail a b}
    (labelling : Labelling site.net (kp .appZero appArg::tail) a b)
    (typed : Typed (kp .appZero appArg::tail)) : Total (kp .appZero appArg::tail) := by
  obtain ⟨shape,_contexts⟩ := app_one_shape labelling typed
  rcases shape with rfl|rfl
  · exact singleton_total _
  · intro input
    exact ⟨input,.cons (.node (g:=site.net) (.inl .appOne) appCtx appArg (.direct (.appArg input))) (.single _ _)⟩
private theorem dummy_one_argument_total {tail a b}
    (labelling : Labelling site.net (kp .appOne appArg::tail) a b) : Total (kp .appOne appArg::tail) := by
  obtain ⟨rfl,_contexts⟩ := binding_stop labelling
  exact singleton_total _
private theorem selected_function_total {tail a b}
    (labelling : Labelling site.net (ac (.inl ())::tail) a b)
    (typed : Typed (ac (.inl ())::tail)) : Total (ac (.inl ())::tail) := by
  obtain ⟨rfl,_contexts⟩ := selected_context_stop labelling typed
  exact singleton_total _
private theorem root_body_total {tail a b}
    (labelling : Labelling site.net (kp .rootLam lamBody::tail) a b)
    (typed : Typed (kp .rootLam lamBody::tail)) : Total (kp .rootLam lamBody::tail) := by
  have whole : Labelling site.net ((.inr (.inl ()))::kp .rootLam lamBody::tail) a b :=
    .cons (.node (g:=site.net) (.inl .rootLam) (.inl ()) lamBody (.direct (.lamBody a))) labelling
  rcases UnpairedRootProof.root_labelling_cases whole rfl with shape|shape|shape
  · cases shape
  · have same : tail=[] := (List.cons.inj (List.cons.inj shape).2).2
    subst tail
    obtain ⟨kind,observed⟩ := typed
    change none=some kind at observed
    cases observed
  · have same : tail=[kp .rootCro (.inl ())] := (List.cons.inj (List.cons.inj shape).2).2
    subst tail
    exact fun input => ⟨input.cons .empty,UnpairedRootProof.loop_labels input⟩

private def properDeparture : (kind : Kind) → Port kind → Bool
  | .op .app,.inl _ => true
  | .op .app,.inr branch => branch
  | .op .lam,.inr branch => branch
  | _,_ => false

private theorem nonroot_program {node : Kept⊕(Unit⊕Unit)} {p : Port (site.net.label node).sort} {tail a b}
    (labelling : Labelling site.net ((.inl ⟨node,p⟩)::tail) a b)
    (typed : Typed ((.inl ⟨node,p⟩)::tail)) (departure : properDeparture (site.net.label node).sort p=true) :
    Total ((.inl ⟨node,p⟩)::tail) ∨
      ((.inl ⟨node,p⟩ : Endpoint site.net)=ac appArg ∧tail=[kp .reader fanO] ∧Traversal 0 (.op .fan) (.inl ()) fanO a b) := by
  rcases node with node |(u|u)
  · cases node with
    | rootLam =>
      cases p with
      | inl u => cases departure
      | inr branch => cases branch with
        | false => cases departure
        | true => exact Or.inl (root_body_total labelling typed)
    | badLam =>
      cases p with
      | inl u => cases departure
      | inr branch => cases branch with
        | false => cases departure
        | true => exact Or.inl (bad_body_total labelling typed)
    | appZero =>
      cases p with
      | inl u => cases u; exact False.elim (garbage_head labelling typed rfl rfl)
      | inr branch => cases branch with
        | false => cases departure
        | true => exact Or.inl (dummy_zero_argument_total labelling typed)
    | appOne =>
      cases p with
      | inl u => cases u; exact False.elim (garbage_head labelling typed rfl rfl)
      | inr branch => cases branch with
        | false => cases departure
        | true => exact Or.inl (dummy_one_argument_total labelling)
    | endLam =>
      cases p with
      | inl u => cases departure
      | inr branch => cases branch with
        | false => cases departure
        | true => exact False.elim (garbage_head labelling typed rfl rfl)
    | rootCro | reader | g0 | g1 | g2 | g3 | g4 | g5 | g6 | g7 | g8 => cases departure
  · cases u
    cases p with
    | inl u => cases u; exact Or.inl (selected_function_total labelling typed)
    | inr branch => cases branch with
      | false => cases departure
      | true => obtain ⟨shape,rule⟩ := reader_shape labelling typed; exact Or.inr ⟨rfl,shape,rule⟩
  · cases u
    cases p with
    | inl u => cases departure
    | inr branch => cases branch with
      | false => cases departure
      | true => exact False.elim (garbage_head labelling typed rfl rfl)
private theorem label_kind_transfer (actual : Label signature) (op : Op) (index : Nat)
    (p : Port actual.sort) (q : Port (.op op)) (lab : actual=label op index) (role : HEq p q) :
    portKind actual.sort p=portKind (.op op) q := by
  subst actual
  cases eq_of_heq role
  rfl
private theorem label_departure_transfer (actual : Label signature) (op : Op) (index : Nat)
    (p : Port actual.sort) (q : Port (.op op)) (lab : actual=label op index) (role : HEq p q) :
    properDeparture actual.sort p=properDeparture (.op op) q := by
  subst actual
  cases eq_of_heq role
  rfl
private theorem incoming_typed {es terminal role level}
    (finish : es.getLast?=some (site.net.wire terminal))
    (atPort : AtProperRole site.net () terminal role level) (incoming : role.incoming) : Typed es := by
  cases atPort with
  | root => exact False.elim incoming
  | appFun | appArg | lamBody => exact False.elim incoming
  | appCtx node p index lab port =>
    refine ⟨.app,?_⟩
    rw [accessKind,finish,Option.bind_some,Pairing.involutive]
    exact label_kind_transfer (site.net.label node) .app _ p appCtx lab port
  | lamCtx node p index lab port =>
    refine ⟨.lam,?_⟩
    rw [accessKind,finish,Option.bind_some,Pairing.involutive]
    exact label_kind_transfer (site.net.label node) .lam _ p (.inl ()) lab port
  | lamBind node p index lab port =>
    refine ⟨.var,?_⟩
    rw [accessKind,finish,Option.bind_some,Pairing.involutive]
    exact label_kind_transfer (site.net.label node) .lam _ p lamBind lab port
private theorem outgoing_departure {node : Kept⊕(Unit⊕Unit)} {p : Port (site.net.label node).sort} {role level}
    (source : AtProperRole site.net () (.inl ⟨node,p⟩) role level) (outgoing : role.outgoing) :
    properDeparture (site.net.label node).sort p=true := by
  cases source with
  | appCtx | lamCtx | lamBind => exact False.elim outgoing
  | appFun node p index lab port => exact label_departure_transfer (site.net.label node) .app _ p (.inl ()) lab port
  | appArg node p index lab port => exact label_departure_transfer (site.net.label node) .app _ p appArg lab port
  | lamBody node p index lab port => exact label_departure_transfer (site.net.label node) .lam _ p lamBody lab port
private theorem node_level {node : Kept⊕(Unit⊕Unit)} {p : Port (site.net.label node).sort} {role level}
    (source : AtProperRole site.net () (.inl ⟨node,p⟩) role level) : (site.net.label node).index=level := by
  cases source with
  | appCtx _ _ _ lab _ | appFun _ _ _ lab _ | appArg _ _ _ lab _
  | lamCtx _ _ _ lab _ | lamBody _ _ _ lab _ | lamBind _ _ _ lab _ => exact congrArg Graph.Label.index lab
private theorem reader_source_level {role level}
    (source : AtProperRole site.net () (ac appArg) role level) : level=1 := (node_level source).symm
private theorem proper_inputs (es : List (Endpoint site.net)) (e f : Endpoint site.net)
    (sr tr : ProperRole) (m n : Nat) (a b : Context)
    (first : es.head?=some e) (finish : es.getLast?=some (site.net.wire f))
    (source : AtProperRole site.net () e sr m) (outgoing : sr.outgoing)
    (target : AtProperRole site.net () f tr n) (incoming : tr.incoming)
    (fw : Forward site.net es) (labelling : Labelling site.net es a b) :
    ∀ replacement,∃ output,Labelling site.net es (a.replace m replacement) output := by
  have typed := incoming_typed finish target incoming
  obtain ⟨tail,rfl⟩ := List.head?_eq_some_iff.mp first
  intro replacement
  rcases e with ⟨node,p⟩ | (u|⟨w,d⟩)
  · have departure := outgoing_departure source outgoing
    rcases nonroot_program labelling typed departure with total |⟨same,shape,rule⟩
    · exact total (a.replace m replacement)
    · have level : m=1 := reader_source_level (by rw [←same]; exact source)
      subst m
      obtain ⟨output,changedRule⟩ := rule.control_inverse_transfer (Or.inl rfl) (a.replace 1 replacement)
        (Context.replace_low _ _ (by decide : 0<1))
      rw [same,shape]
      exact ⟨output,.cons (.node (g:=site.net) (.inl .reader) (.inl ()) fanO changedRule) (.single _ _)⟩
  · cases u
    exact UnpairedRootProof.root_inputs _ a b f tr n labelling fw rfl finish target incoming (a.replace m replacement)
  · exact nomatch w

theorem source_independence : Independence site.net () := by
  intro es e f sr tr m n a b first finish source outgoing target incoming fw labelling
  exact ⟨proper_inputs es e f sr tr m n a b first finish source outgoing target incoming fw labelling,
    indexed.independence_tail () rfl es e f sr tr m n a b first finish source outgoing target incoming fw labelling⟩
#print axioms source_independence
end Lamping.Checks.UnpairedSourceProfiles.Model
namespace Lamping.Checks.UnpairedRootProof
open AG Graph Lambda Lambda.Labelled UnpairedSourceProfiles.Model

theorem model_empty_beta_matches : Matches site.reduce () identity := by
  have fiber : site.betaSyntaxFiber () identity=[] := rfl
  have relative : Marked.RelativeHistory [] (Marked.mark (site.betaSyntaxFiber () identity) identity)
      (Marked.mark [] identity) := by rw [fiber]; exact .nil _
  exact site.beta_complete_matches (original:=initLabels identity) (target:=initLabels identity)
    (marked:=Marked.mark [] identity) (init_is_INIT identity) (by change 0<1; decide)
    root_matches root_inputs flow rfl indexed rfl root_transparency relative
    (by change True; trivial) (.nil _)

#print axioms model_empty_beta_matches
end Lamping.Checks.UnpairedRootProof

namespace Lamping.Checks.UnpairedSourceProfiles.Model
open AG Graph Lambda

/-- This is a real schema application on the entire finite graph, including
its root component and its distinct floating component. -/
theorem actual_beta_step : GraphStep (.beta 1) (ActualNet.ofNet site.net) (ActualNet.ofNet site.reduce) :=
  GraphStep.site labels site

/-- All semantic source hypotheses are proved on this actual graph.
This deliberately makes NO claim that this graph is reachable from an
initial closed encoding. Its root component matches the closed identity. -/
theorem actual_source_properties :
    Independence site.net () ∧RootInputs site.net () ∧Nesting site.net () ∧
      Transparency site.net () ∧Matches site.net () UnpairedRootProof.identity :=
  ⟨source_independence,UnpairedRootProof.root_inputs,indexed.nesting () rfl,
    UnpairedRootProof.root_transparency,UnpairedRootProof.root_matches⟩

/-- The verified graph refutes an overly broad LOCAL preservation premise,
not the reachable-graph theorem or the standard algorithm. The actual beta
rewrite preserves the root Matches I while destroying general proper-source
Independence on the floating component. -/
theorem actual_local_preservation_countermodel :
    Nonempty (FlowBalance site.net (fun _ => true)) ∧
      Nonempty (IndexedLevelBalance site.net (fun _ => 0)) ∧
      Closed UnpairedRootProof.identity ∧
      Independence site.net () ∧RootInputs site.net () ∧Nesting site.net () ∧
      Transparency site.net () ∧Matches site.net () UnpairedRootProof.identity ∧
      GraphStep (.beta 1) (ActualNet.ofNet site.net) (ActualNet.ofNet site.reduce) ∧
      Matches site.reduce () UnpairedRootProof.identity ∧¬Independence site.reduce () := by
  exact ⟨⟨flow⟩,⟨indexed⟩,(by change 0<1; decide),source_independence,UnpairedRootProof.root_inputs,
    indexed.nesting () rfl,UnpairedRootProof.root_transparency,UnpairedRootProof.root_matches,
    actual_beta_step,UnpairedRootProof.model_empty_beta_matches,target_not_independent⟩

#print axioms actual_source_properties
#print axioms actual_beta_step
#print axioms actual_local_preservation_countermodel
end Lamping.Checks.UnpairedSourceProfiles.Model