import Lamping.Lamping.EmptyBetaMatching
import Lamping.Lamping.Fixtures

namespace Lamping.Checks.Phase5Review.EmptyBetaInput
open AG Graph Lambda

private def kept : Bool → Label signature
  | false => label .lam 0
  | true => label .cro 0

/-- A root identity component with its genuine Cro height change, and a
disconnected, balanced beta1 component with one transparent W. -/
def site : PathSite (.beta 1) kept (B:=Unit) (W:=Empty) (V:=Unit) where
  wire := {
    mate := fun e => match e with
      | .inl ⟨.inl false,.inl _⟩ => .inr (.inl ())
      | .inl ⟨.inl false,.inr false⟩ => .inl ⟨.inl true,.inl ()⟩
      | .inl ⟨.inl false,.inr true⟩ => .inl ⟨.inl true,.inr ()⟩
      | .inl ⟨.inl true,.inl _⟩ => .inl ⟨.inl false,lamBind⟩
      | .inl ⟨.inl true,.inr _⟩ => .inl ⟨.inl false,lamBody⟩
      | .inl ⟨.inr (.inl _),.inl _⟩ => .inr (.inr (.inr (),false))
      | .inl ⟨.inr (.inl _),.inr d⟩ => .inl ⟨.inr (.inr ()),.inr (!d)⟩
      | .inl ⟨.inr (.inr _),.inl _⟩ => .inr (.inr (.inr (),true))
      | .inl ⟨.inr (.inr _),.inr d⟩ => .inl ⟨.inr (.inl ()),.inr (!d)⟩
      | .inr (.inl _) => .inl ⟨.inl false,.inl ()⟩
      | .inr (.inr (.inl w,_)) => nomatch w
      | .inr (.inr (.inr _,false)) => .inl ⟨.inr (.inl ()),.inl ()⟩
      | .inr (.inr (.inr _,true)) => .inl ⟨.inr (.inr ()),.inl ()⟩
    involutive := by
      rintro (⟨n|(u|u),p⟩ | (u | ⟨w|v,d⟩))
      · cases n <;> cases p with
        | inl u => cases u; rfl
        | inr d => cases d <;> rfl
      · cases u; cases p with
        | inl u => cases u; rfl
        | inr d => cases d <;> rfl
      · cases u; cases p with
        | inl u => cases u; rfl
        | inr d => cases d <;> rfl
      · cases u; rfl
      · exact nomatch w
      · cases v; cases d <;> rfl
    fixedPointFree := by
      rintro (⟨n|(u|u),p⟩ | (u | ⟨w|v,d⟩)) same
      · cases n <;> cases p with
        | inl u => cases same
        | inr d => cases d <;> cases same
      · cases p <;> cases same
      · cases p <;> cases same
      · cases same
      · exact nomatch w
      · cases d <;> cases same }
  internal := oneWireInternal
  connected := oneWireConnected
  wiring := by
    rintro (b | ⟨v,b⟩)
    · cases b <;> rfl
    · cases v; cases b <;> rfl

def flow : FlowBalance site.net (fun _ => true) where
  nodes := fun _ => true
  vertices := fun _ => false
  wiring := by
    rintro (⟨n|(u|u),p⟩ | (u | ⟨w|v,d⟩))
    · cases n <;> cases p with
      | inl u => cases u; rfl
      | inr d => cases d <;> rfl
    · cases p with
      | inl u => cases u; rfl
      | inr d => cases d <;> rfl
    · cases p with
      | inl u => cases u; rfl
      | inr d => cases d <;> rfl
    · rfl
    · exact nomatch w
    · cases d <;> rfl

def balance : IndexedLevelBalance site.net (fun _ => 0) where
  nodes := fun _ => 0
  vertices := fun _ => 1
  wiring := by
    rintro (⟨n|(u|u),p⟩ | (u | ⟨w|v,d⟩))
    · cases n <;> cases p with
      | inl u => cases u; rfl
      | inr d => cases d <;> rfl
    · cases p with
      | inl u => cases u; rfl
      | inr d => cases d <;> rfl
    · cases p with
      | inl u => cases u; rfl
      | inr d => cases d <;> rfl
    · rfl
    · exact nomatch w
    · cases d <;> rfl
  bounded := by
    rintro (n|(u|u))
    · cases n
      · trivial
      · exact Int.le_refl 0
    · trivial
    · trivial

private abbrev rootEnd : Endpoint site.net := .inr (.inl ())
private abbrev bodyEnd : Endpoint site.net := .inl ⟨.inl false,lamBody⟩
private abbrev croEnd : Endpoint site.net := .inl ⟨.inl true,.inl ()⟩
private abbrev rootPath : List (Endpoint site.net) := [rootEnd]
private abbrev partialPath : List (Endpoint site.net) := [rootEnd,bodyEnd]
private abbrev varPath : List (Endpoint site.net) := [rootEnd,bodyEnd,croEnd]
private abbrev loopPath : List (Endpoint site.net) := [bodyEnd,croEnd]

private theorem partial_labels (a : Context) : Labelling site.net partialPath a a :=
  .cons (LabelledTurn.node (g:=site.net) (.inl false) (.inl ()) lamBody (.direct (.lamBody a))) (.single _ _)

private theorem loop_labels (a : Context) :
    Labelling site.net loopPath a (InitialOffsets.croAt 0 a) :=
  .cons (LabelledTurn.node (g:=site.net) (.inl true) (.inr ()) (.inl ())
    (.direct (InitialOffsets.Event.apply_rel (.cro 0) a))) (.single _ _)

private theorem variable_labels (a : Context) :
    Labelling site.net varPath a (InitialOffsets.croAt 0 a) :=
  .cons (LabelledTurn.node (g:=site.net) (.inl false) (.inl ()) lamBody (.direct (.lamBody a))) (loop_labels a)

/-- Exhaust all actual labelled root paths; the two-node identity component
cannot jump into the disconnected beta component. The control prefix is kept. -/
private theorem root_shapes {es : List (Endpoint site.net)} {a b : Context}
    (labels : Labelling site.net es a b) (rooted : es.head?=some rootEnd) :
    es=rootPath ∨ es=partialPath ∨ es=varPath := by
  obtain ⟨tail,split⟩ := List.head?_eq_some_iff.mp rooted
  subst es
  cases labels with
  | single => exact Or.inl rfl
  | cons first after =>
    cases first with
    | node node p q rule =>
      cases q with
      | inl u => cases u; exact False.elim (rule.distinct rfl)
      | inr d =>
        cases d
        · exact False.elim (rule.no_binding.2 rfl)
        · cases after with
          | single => exact Or.inr (Or.inl rfl)
          | cons next after =>
            cases next with
            | node node p q rule =>
              cases q with
              | inr u => exact False.elim rule.aux_aux
              | inl u =>
                cases u
                cases after with
                | single => exact Or.inr (Or.inr rfl)
                | cons last after =>
                  cases last with
                  | node node p q rule => exact False.elim (rule.no_binding.1 rfl)

theorem source_inputs : RootInputs site.net () := by
  intro es a b terminal role level labels _ rooted _ _ _ requested
  rcases root_shapes labels rooted with rfl | rfl | rfl
  · exact ⟨requested,.single _ _⟩
  · exact ⟨requested,partial_labels requested⟩
  · exact ⟨_,variable_labels requested⟩

private def binding (a : Context) : BindingLoop site.net loopPath a (InitialOffsets.croAt 0 a) where
  binder := .inl false
  isLam := rfl
  body := lamBody
  bind := lamBind
  body_role := HEq.rfl
  bind_role := HEq.rfl
  start := rfl
  finish := rfl
  proper := loop_labels a
  forward := .node (.inl true) (.inr ()) (.inl ()) rfl rfl trivial (.single _)
  shell := by intro n below; change n<0 at below; omega

theorem source_transparency : Transparency site.net () := by
  intro es a b node ctx body bind isLam ctxRole bodyRole bindRole rooted finish _ labels
  have shapes := root_shapes labels rooted
  rcases node with n | (u|u)
  · cases n
    · have hc : ctx=(.inl () : Port (.op .lam)) := eq_of_heq ctxRole
      have hb : body=lamBody := eq_of_heq bodyRole
      have hv : bind=lamBind := eq_of_heq bindRole
      subst ctx; subst body; subst bind
      rcases shapes with rfl | rfl | rfl
      · cases finish
      · cases finish
      · have output := labels.output_unique (variable_labels a)
        subst b
        exact ⟨rootPath,loopPath,a,binding a,rfl,rfl,rfl,.single _ _⟩
    · cases isLam
  · cases isLam
  · cases u
    have hv : bind=lamBind := eq_of_heq bindRole
    subst bind
    rcases shapes with rfl | rfl | rfl <;> cases finish

private def rootAccess : RootAccess site.net () :=
  ⟨rootPath,⟨⟨⟨Context.empty,Context.empty,.single _ _⟩,.single _⟩,rfl,⟨.lam,rfl⟩⟩⟩

private def variableAccess : RootAccess site.net () :=
  ⟨varPath,⟨⟨⟨Context.empty,_,variable_labels Context.empty⟩,
    (variable_labels Context.empty).root_forward_of_flow flow () rfl rfl⟩,rfl,⟨.var,rfl⟩⟩⟩

private theorem variable_suffix : BindingSuffix site.net varPath 0 :=
  ⟨rootPath,loopPath,Context.empty,Context.empty,_,binding Context.empty,
    (.inl ()),rfl,HEq.rfl,rfl,.single _ _,rfl⟩

/-- Source Matches is independently assembled from the exact finite root
path classification, not assumed or obtained from beta preservation. -/
theorem source_matches : Matches site.net () (.lam (.var 0)) := by
  apply matches_of_access_classification
  · intro access
    obtain ⟨a,b,labels⟩ := access.property.1.1
    rcases root_shapes labels access.property.2.1 with same | same | same
    · exact ⟨.lam (.var 0),by rw [same]; rfl,by rw [same]; exact ⟨rfl,trivial⟩⟩
    · have kind := access.property.2.2
      rw [same] at kind
      rcases kind with ⟨k,kind⟩
      cases kind
    · refine ⟨.var 0,by rw [same]; rfl,?_⟩
      rw [same]
      refine ⟨rfl,variable_suffix,?_⟩
      intro j suffix
      exact source_inputs.binding_suffix_unique (balance.nesting () rfl)
        source_transparency variableAccess suffix variable_suffix
  · rintro ⟨p,valid⟩
    cases p with
    | nil => exact ⟨rootAccess,rfl⟩
    | cons step rest =>
      cases step with
      | fn | arg => cases valid
      | body =>
        cases rest with
        | nil => exact ⟨variableAccess,rfl⟩
        | cons step rest => cases step <;> cases valid
  · exact fun _ _ words => source_inputs.accessWord_injective words

theorem fiber_empty : site.betaSyntaxFiber () (.lam (.var 0))=[] := rfl

/-- A nonvacuous complete input instance: all source certificates above are
constructed, and the actual disconnected beta1 rewrite preserves Matches I. -/
theorem actual_empty_beta_matches : Matches site.reduce () (.lam (.var 0)) :=
  site.empty_beta_matches_rootInputs flow () rfl balance rfl source_inputs
    source_transparency source_matches fiber_empty

theorem actual_beta_step : GraphStep (.beta 1)
    (ActualNet.ofNet site.net) (ActualNet.ofNet site.reduce) := GraphStep.site kept site

theorem actual_target_variable : ∃ access : RootAccess site.reduce (),
    accessWord site.reduce access.val=[.body] ∧Observes site.reduce access.val (.var 0) := by
  obtain ⟨access,word,term,lookup,observed⟩ := Matches.observation site.reduce actual_empty_beta_matches
    (⟨[.body],rfl⟩ : Position (.lam (.var 0)))
  change some (.var 0)=some term at lookup
  cases lookup
  exact ⟨access,word,observed⟩

theorem two_actual_source_accesses : rootAccess.val≠variableAccess.val := by
  intro same
  have lengths := congrArg List.length same
  change 1=3 at lengths
  omega

#print axioms source_inputs
#print axioms source_transparency
#print axioms source_matches
#print axioms fiber_empty
#print axioms actual_empty_beta_matches
#print axioms actual_beta_step
#print axioms actual_target_variable
#print axioms two_actual_source_accesses
end Lamping.Checks.Phase5Review.EmptyBetaInput
