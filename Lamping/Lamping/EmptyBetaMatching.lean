import Lamping.Lamping.EmptyBetaBindingAccess
import Lamping.Lamping.RootBetaInputs
import Lamping.Lamping.ReachableTransparency
import Lamping.Lamping.RootBindingSuffixUniqueness
import Lamping.Lamping.RootInputAccessGeometry
import Lamping.Lamping.MatchingInitial
namespace Lamping.AG
open Graph Lambda

private theorem variable_ports (kind : Kind) (p : Port kind) (var : portKind kind p=some .var) :
    ∃ ctx body : Port kind,kind=.op .lam ∧HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      HEq body lamBody ∧HEq p lamBind := by
  cases kind with
  | garbage => cases p; cases var
  | op op =>
    cases op <;> cases p with
    | inl u => cases u; cases var
    | inr d => cases d <;> simp_all [portKind,lamBind]
    all_goals exact ⟨.inl (),lamBody,rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

private theorem suffix_of_binder_eq
    {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    {g : Net signature N D U} {es pre loop : List (Endpoint g)} {a middle b : Context}
    (binding : BindingLoop g loop middle b) (node : N) (binderEq : binding.binder=node)
    (ctx : Port (g.label node).sort) (role : HEq ctx (Sum.inl () : Port (.op .lam)))
    (split : es=pre++loop) (last : pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)))
    (labels : Labelling g pre a middle) : BindingSuffix g es (binderDepth (accessWord g loop)) := by
  rcases binding with ⟨binder,isLam,body,bind,bodyRole,bindRole,start,finish,proper,forward,shell⟩
  dsimp only at binderEq
  subst binder
  exact ⟨pre,loop,a,middle,b,
    ⟨node,isLam,body,bind,bodyRole,bindRole,start,finish,proper,forward,shell⟩,
    ctx,split,role,last,labels,rfl⟩

private theorem variable_suffix
    {N D U : Type} [FiniteNames N] [FiniteNames D] [FiniteNames U]
    {g : Net signature N D U} {root : D} (transparent : Transparency g root)
    (access : RootAccess g root) (kind : accessKind g access.val=some .var) :
    ∃ index,BindingSuffix g access.val index := by
  cases last : access.val.getLast? with
  | none => simp only [accessKind,last,Option.bind_none] at kind; cases kind
  | some e =>
    cases arrival : g.wire e with
    | inr other => simp only [accessKind,last,Option.bind_some,arrival] at kind; cases kind
    | inl node =>
      obtain ⟨node,p⟩ := node
      have actual : portKind (g.label node).sort p=some .var := by
        simpa only [accessKind,last,Option.bind_some,arrival] using kind
      obtain ⟨ctx,body,sort,ctxRole,bodyRole,bindRole⟩ := variable_ports _ p actual
      have finish : access.val.getLast?=some (g.wire (.inl ⟨node,p⟩)) := by
        rw [←arrival,Pairing.involutive]; exact last
      obtain ⟨a,b,labels⟩ := access.property.1.1
      obtain ⟨pre,loop,middle,binding,split,binderEq,preEnd,preLabels⟩ :=
        transparent access.val a b node ctx body p sort ctxRole bodyRole bindRole
          access.property.2.1 finish access.property.1.2 labels
      exact ⟨binderDepth (accessWord g loop),
        suffix_of_binder_eq binding node binderEq ctx ctxRole split preEnd preLabels⟩

section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Label signature} {i : Nat}
variable (site : PathSite (.beta i) kept (B:=B) (W:=W) (V:=V))

/-- Empty old fiber is a semantic stutter of the ACTUAL beta graph rewrite.
Every target property is derived from source RI/T and structural balance;
the variable case transports the original chosen suffix and its index. -/
theorem PathSite.empty_beta_matches_rootInputs
    {directions : B → Bool} {heights : B → Int} (flow : FlowBalance site.net directions)
    (root : B) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net heights) (rootDepth : heights root=0)
    (inputs : RootInputs site.net root) (oldT : Transparency site.net root)
    {t : Term} (matching : Matches site.net root t) (empty : site.betaSyntaxFiber root t=[]) :
    Matches site.reduce root t := by
  have newInputs := site.beta_rootInputs flow root positive balance rootDepth inputs oldT
  obtain ⟨newBalance⟩ := site.reduce_indexed_balance balance
  have newN := newBalance.nesting root rootDepth
  have newT := site.transparency_indexed flow root positive balance rootDepth oldT
  have oldMatching := matching
  obtain ⟨map,corresponds,_prefix⟩ := oldMatching
  apply matches_of_access_classification site.reduce root t
  · intro target
    obtain ⟨kind,observedKind⟩ := target.property.2.2
    cases kind with
    | app | lam =>
      all_goals
        obtain ⟨source,word,kind⟩ := site.empty_beta_access_backward matching flow positive oldT empty target
        obtain ⟨sourceWord,u,lookup,observed⟩ := corresponds source
        have lookupTarget : subtermAt t (accessWord site.reduce target.val)=some u := by
          rw [←word,sourceWord]; exact lookup
        have actualKind := observed.1.symm.trans (kind.trans observedKind)
        cases u with
        | var index => cases actualKind
        | app fn arg =>
          first | exact ⟨_,lookupTarget,observedKind,trivial⟩ | cases actualKind
        | lam body =>
          first | exact ⟨_,lookupTarget,observedKind,trivial⟩ | cases actualKind
    | var =>
      obtain ⟨index,targetSuffix⟩ := variable_suffix newT target observedKind
      obtain ⟨source,word,kind,sourceSuffix⟩ :=
        site.empty_beta_binding_access_backward matching flow positive oldT empty target targetSuffix
      obtain ⟨sourceWord,u,lookup,observed⟩ := corresponds source
      have lookupTarget : subtermAt t (accessWord site.reduce target.val)=some u := by
        rw [←word,sourceWord]; exact lookup
      have sameKind : (syntaxShape u).kind=.var :=
        Option.some.inj (observed.1.symm.trans (kind.trans observedKind))
      cases u with
      | app fn arg => cases sameKind
      | lam body => cases sameKind
      | var sourceIndex =>
        have indices : index=sourceIndex := observed.2.2 index sourceSuffix
        subst index
        exact ⟨_,lookupTarget,observedKind,targetSuffix,
          fun other otherSuffix => newInputs.binding_suffix_unique newN newT target otherSuffix targetSuffix⟩
  · intro position
    obtain ⟨source,sourceWord,_⟩ := Matches.observation site.net matching position
    obtain ⟨target,targetWord,_⟩ := site.empty_beta_access_forward matching flow positive oldT empty source
    exact ⟨target,targetWord.trans sourceWord⟩
  · exact fun _ _ words => newInputs.accessWord_injective words
end
end Lamping.AG

