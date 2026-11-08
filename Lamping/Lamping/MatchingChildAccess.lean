import Lamping.Lamping.MatchingUniqueness
import Lamping.Lamping.InitialAccessWords
import Lamping.Lamping.TraceSeams
namespace Lamping.AG
open Graph Lambda

private theorem flatMap_last_token {T : Type} (token : T → Path)
    (small : ∀ x,(token x).length≤1) (xs : List T) (word : Path)
    (whole : xs.flatMap token=word++[.fn]) :
    ∃ pre item tail,xs=pre++item::tail ∧pre.flatMap token=word ∧
      token item=[.fn] ∧tail.flatMap token=[] := by
  induction xs generalizing word with
  | nil => have impossible := congrArg List.length whole; simp at impossible
  | cons x xs ih =>
    cases hx : token x with
    | nil =>
      have rest : xs.flatMap token=word++[.fn] := by simpa only [List.flatMap_cons,hx,List.nil_append] using whole
      obtain ⟨pre,item,tail,split,prefixWord,atToken,endWord⟩ := ih word rest
      exact ⟨x::pre,item,tail,by simp only [split,List.cons_append],
        by simp only [List.flatMap_cons,hx,List.nil_append,prefixWord],atToken,endWord⟩
    | cons symbol symbols =>
      have length := small x
      rw [hx,List.length_cons] at length
      have empty : symbols=[] := List.length_eq_zero_iff.mp (by omega)
      subst symbols
      have decomposed : symbol::xs.flatMap token=word++[.fn] := by
        simpa only [List.flatMap_cons,hx,List.singleton_append] using whole
      cases word with
      | nil =>
        have parts := List.cons.inj decomposed
        have same := parts.1
        subst symbol
        exact ⟨[],x,xs,rfl,rfl,hx,parts.2⟩
      | cons w word =>
        have parts := List.cons.inj decomposed
        have same : symbol=w := parts.1
        subst symbol
        obtain ⟨pre,item,tail,split,prefixWord,atToken,endWord⟩ := ih word parts.2
        exact ⟨x::pre,item,tail,by simp only [split,List.cons_append],
          by simp only [List.flatMap_cons,hx,List.singleton_append,prefixWord],atToken,endWord⟩

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem arrivalWord_small (e : Endpoint g) : (arrivalWord g e).length≤1 := by
  rcases e with ⟨node,p⟩ | (boundary | vertex)
  · unfold arrivalWord
    repeat (first | split | decide)
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- Def.3.5.13's actual bijection forces physical equality of proper-ended
accesses with the same syntax word. No converse prefix property is assumed. -/
theorem Matches.accessWord_injective {t : Term} (matching : Matches g root t) :
    Function.Injective (fun access : RootAccess g root => accessWord g access.val) := by
  obtain ⟨bijection,corresponds,_⟩ := matching
  intro left right same
  apply bijection.injective
  apply Subtype.ext
  exact (corresponds left).1.symm.trans (same.trans (corresponds right).1)

private def departureToken : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem fn_token_ports (kind : Kind) (p q : Port kind)
    (direction : ForwardPorts kind p q) (token : departureToken kind q=[.fn]) :
    kind=.op .app ∧HEq p appCtx ∧HEq q (Sum.inl () : Port (.op .app)) := by
  cases kind with
  | garbage => cases token
  | op op =>
    cases op with
    | app =>
      cases q with
      | inl point => cases point; exact ⟨rfl,heq_of_eq direction.1,HEq.rfl⟩
      | inr branch => cases branch <;> cases token
    | lam =>
      cases q with
      | inl point => cases point; cases token
      | inr branch => cases branch <;> cases token
    | fan => cases token
    | cro => cases token
    | bra => cases token

private theorem label_app_of_sort (actual : Label signature) (sort : actual.sort=.op .app) :
    actual=label .app actual.index := by
  cases actual with
  | mk kind index => cases sort; rfl

/-- Reflect the actual ordinary turn immediately before a function token.
The preceding physical prefix ends at that very application's context. -/
private theorem Forward.before_function_token {pre tail : List (Endpoint g)} {f : Endpoint g}
    (forward : Forward g (pre++f::tail)) (nonempty : pre≠[]) (token : arrivalWord g f=[.fn]) :
    ∃ (node : N) (ctx funPort : Port (g.label node).sort),
      g.label node=label .app (g.label node).index ∧HEq ctx appCtx ∧
      HEq funPort (Sum.inl () : Port (.op .app)) ∧
      pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) ∧f=.inl ⟨node,funPort⟩ := by
  induction pre with
  | nil => exact False.elim (nonempty rfl)
  | cons e pre ih =>
    cases pre with
    | nil =>
      cases forward with
      | node node p q arrives leaves direction rest =>
        have token' : departureToken (g.label node).sort q=[.fn] := by
          rw [leaves] at token
          exact token
        obtain ⟨sort,ctxRole,funRole⟩ := fn_token_ports _ p q direction token'
        have endpoint : e=g.wire (.inl ⟨node,p⟩) := by
          have wired := congrArg g.wire.mate arrives
          simpa only [Pairing.involutive] using wired
        exact ⟨node,p,q,label_app_of_sort _ sort,ctxRole,funRole,congrArg some endpoint,leaves⟩
      | transparent vertex direction arrives leaves rest =>
        rw [leaves] at token
        cases token
    | cons x pre =>
      have tailForward : Forward g ((x::pre)++f::tail) := by
        cases forward with
        | node node p q arrives leaves direction rest => exact rest
        | transparent vertex direction arrives leaves rest => exact rest
      obtain ⟨node,ctx,funPort,lab,ctxRole,funRole,finish,atFun⟩ := ih tailForward (by simp)
      exact ⟨node,ctx,funPort,lab,ctxRole,funRole,by simpa only [List.getLast?_cons_cons] using finish,atFun⟩

private theorem app_context_kind (actual : Label signature) (p : Port actual.sort) (index : Nat)
    (lab : actual=label .app index) (role : HEq p appCtx) : portKind actual.sort p=some .app := by
  subst actual
  have same : p=appCtx := eq_of_heq role
  subst p
  rfl

/-- Cut at the actual final function token. The prefix is itself a genuine
proper-ended root access, with app kind and exactly the preceding word. -/
theorem RootAccess.before_function_token (access : RootAccess g root) (word : Path)
    (whole : accessWord g access.val=word++[.fn]) :
    ∃ (parent : RootAccess g root) (node : N) (ctx funPort : Port (g.label node).sort) (tail : List (Endpoint g)),
      g.label node=label .app (g.label node).index ∧HEq ctx appCtx ∧
      HEq funPort (Sum.inl () : Port (.op .app)) ∧
      accessWord g parent.val=word ∧accessKind g parent.val=some .app ∧
      parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) ∧
      access.val=parent.val++(.inl ⟨node,funPort⟩)::tail := by
  have tokens : access.val.flatMap (arrivalWord g)=word++[.fn] :=
    (accessTokens_eq_accessWord g root access.property.2.1).trans whole
  obtain ⟨pre,f,tail,split,prefixTokens,token,_⟩ := flatMap_last_token (arrivalWord g) arrivalWord_small _ word tokens
  have nonempty : pre≠[] := by
    intro empty
    have first : access.val.head?=some f := by rw [split,empty]; rfl
    have equal : f=.inr (.inl root) := Option.some.inj (first.symm.trans access.property.2.1)
    rw [equal] at token
    cases token
  have preRoot : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (nonempty rfl)
    | cons e pre => simpa only [split,List.cons_append,List.head?_cons] using access.property.2.1
  have forward := access.property.1.2
  rw [split] at forward
  obtain ⟨node,ctx,funPort,lab,ctxRole,funRole,finish,atFun⟩ := forward.before_function_token nonempty token
  obtain ⟨a,b,labels⟩ := access.property.1.1
  rw [split] at labels
  obtain ⟨middle,prefixLabels⟩ := labels.prefix nonempty
  have preForward := forward.prefix_of_append nonempty
  have kind : accessKind g pre=some .app := by
    unfold accessKind
    rw [finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact app_context_kind _ ctx _ lab ctxRole
  let parent : RootAccess g root := ⟨pre,⟨⟨⟨a,middle,prefixLabels⟩,preForward⟩,preRoot,⟨.app,kind⟩⟩⟩
  refine ⟨parent,node,ctx,funPort,tail,lab,ctxRole,funRole,?_,kind,finish,?_⟩
  · exact (accessTokens_eq_accessWord g root preRoot).symm.trans prefixTokens
  · rw [split,atFun]

/-- The syntax function child supplies a specific actual typed access which
extends this very application prefix and its actual function departure.
The remaining tail may be empty. This is not completion of a control tail. -/
theorem Matches.function_child_access {t : Term} (matching : Matches g root t)
    (parent : RootAccess g root) (node : N) (ctx funPort : Port (g.label node).sort) (index : Nat)
    (lab : g.label node=label .app index) (ctxRole : HEq ctx appCtx)
    (funRole : HEq funPort (Sum.inl () : Port (.op .app)))
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
    ∃ (child : RootAccess g root) (tail : List (Endpoint g)),
      child.val=parent.val++(.inl ⟨node,funPort⟩)::tail ∧
      accessWord g child.val=accessWord g parent.val++[.fn] := by
  have kind : accessKind g parent.val=some .app := by
    unfold accessKind
    rw [finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact app_context_kind _ ctx index lab ctxRole
  have injective := matching.accessWord_injective
  obtain ⟨bijection,corresponds,_⟩ := matching
  obtain ⟨subterm,lookup,observes⟩ := (corresponds parent).2
  have shape : (syntaxShape subterm).kind=.app := Option.some.inj (observes.1.symm.trans kind)
  cases subterm with
  | var k => cases shape
  | lam body => cases shape
  | app function argument =>
    have lookupWord : subtermAt t (accessWord g parent.val)=some (.app function argument) := by
      rw [(corresponds parent).1]
      exact lookup
    let position : Position t := ⟨accessWord g parent.val++[.fn],by
      rw [subtermAt_append,lookupWord]
      cases function <;> rfl⟩
    let child := bijection.invFun position
    have childWord : accessWord g child.val=accessWord g parent.val++[.fn] := by
      have word := (corresponds child).1
      rw [show bijection child=position from bijection.right_inv position] at word
      exact word
    obtain ⟨actualParent,actualNode,actualCtx,actualFun,tail,_,_,actualFunRole,parentWord,_,actualFinish,split⟩ :=
      child.before_function_token (accessWord g parent.val) childWord
    have parentEq : actualParent=parent := injective parentWord
    rw [parentEq] at actualFinish split
    have endpoint : (.inl ⟨actualNode,actualCtx⟩ : Endpoint g)=.inl ⟨node,ctx⟩ := by
      have wireEqual := Option.some.inj (actualFinish.symm.trans finish)
      have original := congrArg g.wire.mate wireEqual
      simpa only [Pairing.involutive] using original
    have nodes : actualNode=node := congrArg Sigma.fst (Sum.inl.inj endpoint)
    subst actualNode
    have ports : actualFun=funPort := eq_of_heq (actualFunRole.trans funRole.symm)
    rw [ports] at split
    exact ⟨child,tail,split,childWord⟩
end
end Lamping.AG



