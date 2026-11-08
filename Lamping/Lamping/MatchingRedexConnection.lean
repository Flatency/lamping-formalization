import Lamping.Lamping.MatchingChildAccess
import Lamping.Lamping.MatchedControlInputs
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem app_kind (actual : Label signature) (p : Port actual.sort) (i : Nat)
    (lab : actual=label .app i) (role : HEq p appCtx) : portKind actual.sort p=some .app := by
  subst actual
  have same : p=appCtx := eq_of_heq role
  subst p; rfl
private theorem bind_kind (actual : Label signature) (p : Port actual.sort) (i : Nat)
    (lab : actual=label .lam i) (role : HEq p lamBind) : portKind actual.sort p=some .var := by
  subst actual
  have same : p=lamBind := eq_of_heq role
  subst p; rfl

/-- A lambda observation selects a real lambda context endpoint, including
its actual index and principal port, rather than only a printed access kind. -/
theorem RootAccess.lambda_endpoint (path : RootAccess g root)
    (kind : accessKind g path.val=some .lam) :
    ∃ (node : N) (p : Port (g.label node).sort) (i : Nat),
      g.label node=label .lam i ∧HEq p (Sum.inl () : Port (.op .lam)) ∧
      path.val.getLast?=some (g.wire (.inl ⟨node,p⟩)) := by
  obtain ⟨terminal,role,level,finish,atPort,incoming⟩ := path.incoming_endpoint
  cases atPort with
  | root => exact False.elim incoming
  | appFun => exact False.elim incoming
  | appArg => exact False.elim incoming
  | lamBody => exact False.elim incoming
  | appCtx node p i lab port =>
    have actual : portKind (g.label node).sort p=some .lam := by
      simpa only [accessKind,finish,Option.bind_some,Pairing.involutive] using kind
    rw [app_kind _ p level lab port] at actual
    cases actual
  | lamBind node p i lab port =>
    have actual : portKind (g.label node).sort p=some .lam := by
      simpa only [accessKind,finish,Option.bind_some,Pairing.involutive] using kind
    rw [bind_kind _ p level lab port] at actual
    cases actual
  | lamCtx node p i lab port => exact ⟨node,p,level,lab,port,finish⟩

private def portArrival : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem function_word (actual : Label signature) (p : Port actual.sort) (i : Nat)
    (lab : actual=label .app i) (role : HEq p (Sum.inl () : Port (.op .app))) :
    portArrival actual.sort p=[.fn] := by
  subst actual
  have same : p=Sum.inl () := eq_of_heq role
  subst p; rfl

/-- Actual geometry extracted from one syntax redex: an ordinary properly
labelled forward path from the app principal to the lambda context. Its word
is empty because the already consumed app function token is skipped. -/
structure RedexConnection (g : Net signature N B W) where
  app : N
  lam : N
  appPort : Port (g.label app).sort
  lamPort : Port (g.label lam).sort
  appIndex : Nat
  lamIndex : Nat
  appLabel : g.label app=label .app appIndex
  lamLabel : g.label lam=label .lam lamIndex
  appPrincipal : HEq appPort (Sum.inl () : Port (.op .app))
  lamPrincipal : HEq lamPort (Sum.inl () : Port (.op .lam))
  edges : List (Endpoint g)
  proper : ForwardProperPath g edges
  start : edges.head?=some (.inl ⟨app,appPort⟩)
  finish : edges.getLast?=some (g.wire (.inl ⟨lam,lamPort⟩))
  emptyWord : accessWord g edges=[]

/-- A real redex in the matching syntax tree gives the actual connecting
proper path. This theorem constructs it from Matches; no Independence or
arbitrary path-extension assertion is used. -/
theorem Matches.redex_connection {t : Term} (matching : Matches g root t) (redex : RedexOcc t) :
    Nonempty (RedexConnection g) := by
  obtain ⟨u,lookup,isRedex⟩ := redex.property
  obtain ⟨body,argument,actualLookup⟩ :
      ∃ body argument,subtermAt t redex.val=some (.app (.lam body) argument) := by
    cases u with
    | var i => exact False.elim isRedex
    | lam b => exact False.elim isRedex
    | app function argument =>
      cases function with
      | var i => exact False.elim isRedex
      | app f a => exact False.elim isRedex
      | lam b => exact ⟨b,argument,lookup⟩
  let childPosition : Position t := ⟨redex.val++[.fn],by
    rw [subtermAt_append,actualLookup]; rfl⟩
  obtain ⟨child,childWord,v,childLookup,childObservation⟩ := Matches.observation g matching childPosition
  have lamLookup : subtermAt t childPosition.val=some (.lam body) := by
    rw [subtermAt_append,actualLookup]; rfl
  have same : v=.lam body := Option.some.inj (childLookup.symm.trans lamLookup)
  subst v
  have lambdaKind : accessKind g child.val=some .lam := childObservation.1
  obtain ⟨lam,lamPort,lamIndex,lamLabel,lamRole,lamEnd⟩ := child.lambda_endpoint lambdaKind
  obtain ⟨parent,app,ctx,appPort,tail,appLabel,_ctxRole,appRole,parentWord,_parentKind,
      _parentEnd,split⟩ := child.before_function_token redex.val childWord
  have token : arrivalWord g (.inl ⟨app,appPort⟩)=[.fn] :=
    function_word (g.label app) appPort (g.label app).index appLabel appRole
  have tokens : child.val.flatMap (arrivalWord g)=redex.val++[.fn] :=
    (accessTokens_eq_accessWord g root child.property.2.1).trans childWord
  have parentTokens : parent.val.flatMap (arrivalWord g)=redex.val :=
    (accessTokens_eq_accessWord g root parent.property.2.1).trans parentWord
  rw [split,List.flatMap_append,List.flatMap_cons,token,parentTokens] at tokens
  have onlyToken := List.append_cancel_left tokens
  have noTail : tail.flatMap (arrivalWord g)=[] := by
    simpa only [List.singleton_append,List.cons.injEq,true_and] using onlyToken
  obtain ⟨a,b,labels⟩ := child.property.1.1
  rw [split] at labels
  obtain ⟨middle,_prefix,suffix⟩ := labels.split_segment
  have atSource : child.val[parent.val.length]?=some (.inl ⟨app,appPort⟩) := by
    rw [split,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]; rfl
  have forward := child.property.1.2.suffix_at parent.val.length _ atSource
  rw [split,List.drop_append,List.drop_length,Nat.sub_self,List.drop_zero,List.nil_append] at forward
  have finish : ((.inl ⟨app,appPort⟩)::tail).getLast?=some (g.wire (.inl ⟨lam,lamPort⟩)) := by
    rw [split,List.getLast?_append] at lamEnd
    simpa only [List.getLast?_cons,Option.some_or] using lamEnd
  exact ⟨{
    app := app, lam := lam, appPort := appPort, lamPort := lamPort,
    appIndex := (g.label app).index, lamIndex := lamIndex,
    appLabel := appLabel, lamLabel := lamLabel,
    appPrincipal := appRole, lamPrincipal := lamRole,
    edges := (.inl ⟨app,appPort⟩)::tail,
    proper := ⟨⟨middle,b,suffix⟩,forward⟩,start := rfl,finish := finish,emptyWord := noTail }⟩
end
end Lamping.AG
