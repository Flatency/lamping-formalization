import Lamping.Lamping.MatchingRedexConnection
import Lamping.Lamping.MatchingSubtermAccess
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
/-- A connecting path with its actual source syntax occurrence and literal
root accesses. Unlike a bare connection, this retains occurrence provenance. -/
structure ActualRedexAccess (g : Net signature N B W) (root : B) {t : Term} (redex : RedexOcc t) where
  connection : RedexConnection g
  parent : RootAccess g root
  child : RootAccess g root
  ctx : Port (g.label connection.app).sort
  contextPrincipal : HEq ctx appCtx
  parentWord : accessWord g parent.val=redex.val
  childWord : accessWord g child.val=redex.val++[.fn]
  parentFinish : parent.val.getLast?=some (g.wire (.inl ⟨connection.app,ctx⟩))
  split : child.val=parent.val++connection.edges
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


/-- Source Matches constructs the full literal provenance of a particular
actual syntax redex, including the properly labelled connection suffix. -/
theorem Matches.actual_redex_access {t : Term} (matching : Matches g root t) (redex : RedexOcc t) :
    Nonempty (ActualRedexAccess g root redex) := by
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
  obtain ⟨parent,app,ctx,appPort,tail,appLabel,ctxRole,appRole,parentWord,_parentKind,
      parentEnd,split⟩ := child.before_function_token redex.val childWord
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
  let connection : RedexConnection g := {
    app := app, lam := lam, appPort := appPort, lamPort := lamPort,
    appIndex := (g.label app).index, lamIndex := lamIndex,
    appLabel := appLabel, lamLabel := lamLabel,
    appPrincipal := appRole, lamPrincipal := lamRole,
    edges := (.inl ⟨app,appPort⟩)::tail,
    proper := ⟨⟨middle,b,suffix⟩,forward⟩,start := rfl,finish := finish,emptyWord := noTail }
  exact ⟨⟨connection,parent,child,ctx,ctxRole,parentWord,childWord,parentEnd,split⟩⟩
private theorem same_wire_node {a b : N} {p : Port (g.label a).sort} {q : Port (g.label b).sort}
    (eq : g.wire (.inl ⟨a,p⟩)=g.wire (.inl ⟨b,q⟩)) : a=b := by
  have endpoints := congrArg (fun e => g.wire e) eq
  simp only [Pairing.involutive] at endpoints
  exact congrArg Sigma.fst (Sum.inl.inj endpoints)
/-- Provenance, not the empty word of an arbitrary connection, locks both
literal root accesses and the physical application/lambda endpoints. -/
theorem ActualRedexAccess.endpoints_unique {t : Term} {redex : RedexOcc t}
    (matching : Matches g root t) (first second : ActualRedexAccess g root redex) :
    first.parent=second.parent ∧ first.child=second.child ∧
      first.connection.app=second.connection.app ∧ first.connection.lam=second.connection.lam := by
  have parents : first.parent=second.parent := matching.accessWord_injective
    (first.parentWord.trans second.parentWord.symm)
  have children : first.child=second.child := matching.accessWord_injective
    (first.childWord.trans second.childWord.symm)
  have apps : first.connection.app=second.connection.app := same_wire_node
    (Option.some.inj (first.parentFinish.symm.trans (parents ▸ second.parentFinish)))
  have finishes (w : ActualRedexAccess g root redex) :
      w.child.val.getLast?=some (g.wire (.inl ⟨w.connection.lam,w.connection.lamPort⟩)) := by
    rw [w.split,List.getLast?_append,w.connection.finish]
    rfl
  have lams : first.connection.lam=second.connection.lam := same_wire_node
    (Option.some.inj ((finishes first).symm.trans (children ▸ finishes second)))
  exact ⟨parents,children,apps,lams⟩
end
end Lamping.AG




