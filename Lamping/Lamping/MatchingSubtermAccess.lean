import Lamping.Lamping.MatchingChildAccess
namespace Lamping.AG
open Graph Lambda

/-- The three actual syntax-child passages. This records physical ports,
not a certificate that an arbitrary path can be completed. -/
inductive SyntaxChildPorts : (kind : Kind) → Port kind → Port kind → Step → Prop where
  | function : SyntaxChildPorts (.op .app) appCtx (.inl ()) .fn
  | argument : SyntaxChildPorts (.op .app) appCtx appArg .arg
  | body : SyntaxChildPorts (.op .lam) (.inl ()) lamBody .body

private def childParentKind : Step → AccessKind
  | .fn | .arg => .app
  | .body => .lam

private theorem SyntaxChildPorts.parent_kind (roles : SyntaxChildPorts kind ctx child step) :
    portKind kind ctx=some (childParentKind step) := by cases roles <;> rfl
private theorem SyntaxChildPorts.child_unique (left : SyntaxChildPorts kind ctx child step)
    (right : SyntaxChildPorts kind ctx' child' step) : child=child' := by
  cases left <;> cases right <;> rfl

private theorem SyntaxChildPorts.child_exists (roles : SyntaxChildPorts kind ctx child step)
    (subterm : Term) (shape : (syntaxShape subterm).kind=childParentKind step) :
    ∃ u,subtermAt subterm [step]=some u := by
  cases roles <;> cases subterm <;> simp_all [syntaxShape,AccessShape.kind,childParentKind,subtermAt]

private theorem flatMap_last_syntax_token {T : Type} (token : T → Path)
    (small : ∀ x,(token x).length≤1) (xs : List T) (word : Path) (step : Step)
    (whole : xs.flatMap token=word++[step]) :
    ∃ pre item tail,xs=pre++item::tail ∧ pre.flatMap token=word ∧ token item=[step] ∧ tail.flatMap token=[] := by
  induction xs generalizing word with
  | nil => have impossible := congrArg List.length whole; simp at impossible
  | cons x xs ih =>
    cases hx : token x with
    | nil =>
      have rest : xs.flatMap token=word++[step] := by simpa only [List.flatMap_cons,hx,List.nil_append] using whole
      obtain ⟨pre,item,tail,split,prefixWord,atToken,endWord⟩ := ih word rest
      exact ⟨x::pre,item,tail,by simp only [split,List.cons_append],
        by simp only [List.flatMap_cons,hx,List.nil_append,prefixWord],atToken,endWord⟩
    | cons symbol symbols =>
      have length := small x
      rw [hx,List.length_cons] at length
      have empty : symbols=[] := List.length_eq_zero_iff.mp (by omega)
      subst symbols
      have decomposed : symbol::xs.flatMap token=word++[step] := by simpa only [List.flatMap_cons,hx,List.singleton_append] using whole
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

private def childDepartureToken : (kind : Kind) → Port kind → Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem child_token_ports (kind : Kind) (p q : Port kind) (step : Step)
    (direction : ForwardPorts kind p q) (token : childDepartureToken kind q=[step]) :
    SyntaxChildPorts kind p q step := by
  cases kind with
  | garbage => cases direction
  | op op =>
    cases op with
    | app =>
      cases q with
      | inl point =>
        cases point
        have same : Step.fn=step := (List.cons.inj token).1
        cases same
        rw [direction.1]
        exact .function
      | inr branch =>
        cases branch with
        | false => cases token
        | true =>
          have same : Step.arg=step := (List.cons.inj token).1
          cases same
          rw [direction.1]
          exact .argument
    | lam =>
      cases q with
      | inl point => cases point; cases token
      | inr branch =>
        cases branch with
        | false => cases token
        | true =>
          have same : Step.body=step := (List.cons.inj token).1
          cases same
          rw [direction.1]
          exact .body
    | fan | cro | bra => cases token

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

private theorem child_arrivalWord_small (e : Endpoint g) : (arrivalWord g e).length≤1 := by
  rcases e with ⟨node,p⟩ | (boundary | vertex)
  · unfold arrivalWord
    repeat (first | split | decide)
  · exact Nat.zero_le _
  · exact Nat.zero_le _

private theorem Forward.before_syntax_token {pre tail : List (Endpoint g)} {f : Endpoint g}
    (forward : Forward g (pre++f::tail)) (nonempty : pre≠[]) (token : arrivalWord g f=[step]) :
    ∃ (node : N) (ctx child : Port (g.label node).sort),
      SyntaxChildPorts (g.label node).sort ctx child step ∧
      pre.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) ∧ f=.inl ⟨node,child⟩ := by
  induction pre with
  | nil => exact False.elim (nonempty rfl)
  | cons e pre ih =>
    cases pre with
    | nil =>
      cases forward with
      | node node p q arrives leaves direction rest =>
        have token' : childDepartureToken (g.label node).sort q=[step] := by rw [leaves] at token; exact token
        have roles := child_token_ports _ p q step direction token'
        have endpoint : e=g.wire (.inl ⟨node,p⟩) := by
          have wired := congrArg g.wire.mate arrives
          simpa only [Pairing.involutive] using wired
        exact ⟨node,p,q,roles,congrArg some endpoint,leaves⟩
      | transparent vertex direction arrives leaves rest => rw [leaves] at token; cases token
    | cons x pre =>
      have tailForward : Forward g ((x::pre)++f::tail) := by
        cases forward with
        | node node p q arrives leaves direction rest => exact rest
        | transparent vertex direction arrives leaves rest => exact rest
      obtain ⟨node,ctx,child,roles,finish,atChild⟩ := ih tailForward (by simp)
      exact ⟨node,ctx,child,roles,by simpa only [List.getLast?_cons_cons] using finish,atChild⟩

/-- Cut the exact last syntax token of an existing rooted access. The
returned parent is itself a real proper-ended access at that same node. -/
theorem RootAccess.before_syntax_token (access : RootAccess g root) (word : Path) (step : Step)
    (whole : accessWord g access.val=word++[step]) :
    ∃ (parent : RootAccess g root) (node : N) (ctx child : Port (g.label node).sort) (tail : List (Endpoint g)),
      SyntaxChildPorts (g.label node).sort ctx child step ∧
      accessWord g parent.val=word ∧ parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) ∧
      access.val=parent.val++(.inl ⟨node,child⟩)::tail := by
  have tokens : access.val.flatMap (arrivalWord g)=word++[step] :=
    (accessTokens_eq_accessWord g root access.property.2.1).trans whole
  obtain ⟨pre,f,tail,split,prefixTokens,token,_⟩ := flatMap_last_syntax_token (arrivalWord g) child_arrivalWord_small _ word step tokens
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
  obtain ⟨node,ctx,child,roles,finish,atChild⟩ := forward.before_syntax_token nonempty token
  obtain ⟨a,b,labels⟩ := access.property.1.1
  rw [split] at labels
  obtain ⟨middle,prefixLabels⟩ := labels.prefix nonempty
  have preForward := forward.prefix_of_append nonempty
  have kind : accessKind g pre=some (childParentKind step) := by
    unfold accessKind
    rw [finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact roles.parent_kind
  let parent : RootAccess g root := ⟨pre,⟨⟨⟨a,middle,prefixLabels⟩,preForward⟩,preRoot,⟨_,kind⟩⟩⟩
  refine ⟨parent,node,ctx,child,tail,roles,?_,finish,?_⟩
  · exact (accessTokens_eq_accessWord g root preRoot).symm.trans prefixTokens
  · rw [split,atChild]

/-- A specified actual parent and one of its three physical syntax ports
has a particular existing matching child access. This derives the exact
prefix from Matches; it does not extend an arbitrary control tail. -/
theorem Matches.child_access {t : Term} (matching : Matches g root t)
    (parent : RootAccess g root) (node : N) (ctx childPort : Port (g.label node).sort) (step : Step)
    (roles : SyntaxChildPorts (g.label node).sort ctx childPort step)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
    ∃ (child : RootAccess g root) (tail : List (Endpoint g)),
      child.val=parent.val++(.inl ⟨node,childPort⟩)::tail ∧
      accessWord g child.val=accessWord g parent.val++[step] := by
  have kind : accessKind g parent.val=some (childParentKind step) := by
    unfold accessKind
    rw [finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact roles.parent_kind
  have injective := matching.accessWord_injective
  obtain ⟨bijection,corresponds,_⟩ := matching
  obtain ⟨subterm,lookup,observes⟩ := (corresponds parent).2
  have shape : (syntaxShape subterm).kind=childParentKind step := Option.some.inj (observes.1.symm.trans kind)
  have childExists : ∃ u,subtermAt subterm [step]=some u := roles.child_exists subterm shape
  obtain ⟨childTerm,childLookup⟩ := childExists
  have lookupWord : subtermAt t (accessWord g parent.val)=some subterm := by
    rw [(corresponds parent).1]
    exact lookup
  let position : Position t := ⟨accessWord g parent.val++[step],by
    rw [subtermAt_append,lookupWord]
    simp only [Option.bind_some,childLookup,Option.isSome_some]⟩
  let child := bijection.invFun position
  have childWord : accessWord g child.val=accessWord g parent.val++[step] := by
    have word := (corresponds child).1
    rw [show bijection child=position from bijection.right_inv position] at word
    exact word
  obtain ⟨actualParent,actualNode,actualCtx,actualChild,tail,actualRoles,parentWord,actualFinish,split⟩ :=
    child.before_syntax_token (accessWord g parent.val) step childWord
  have parentEq : actualParent=parent := injective parentWord
  rw [parentEq] at actualFinish split
  have endpoint : (.inl ⟨actualNode,actualCtx⟩ : Endpoint g)=.inl ⟨node,ctx⟩ := by
    have wireEqual := Option.some.inj (actualFinish.symm.trans finish)
    have original := congrArg g.wire.mate wireEqual
    simpa only [Pairing.involutive] using original
  have nodes : actualNode=node := congrArg Sigma.fst (Sum.inl.inj endpoint)
  subst actualNode
  have ports : actualChild=childPort := actualRoles.child_unique roles
  rw [ports] at split
  exact ⟨child,tail,split,childWord⟩
end

/-- Caller-friendly physical roles for the argument passage. -/
theorem SyntaxChildPorts.argument_roles (roles : SyntaxChildPorts kind ctx child .arg) :
    kind=.op .app ∧ HEq ctx appCtx ∧ HEq child appArg := by cases roles; exact ⟨rfl,HEq.rfl,HEq.rfl⟩
theorem SyntaxChildPorts.body_roles (roles : SyntaxChildPorts kind ctx child .body) :
    kind=.op .lam ∧ HEq ctx (Sum.inl () : Port (.op .lam)) ∧ HEq child lamBody := by
  cases roles; exact ⟨rfl,HEq.rfl,HEq.rfl⟩
private theorem SyntaxChildPorts.of_argument (shape : kind=.op .app)
    (ctxRole : HEq ctx appCtx) (childRole : HEq child appArg) : SyntaxChildPorts kind ctx child .arg := by
  subst kind
  have hc : ctx=appCtx := eq_of_heq ctxRole
  have hd : child=appArg := eq_of_heq childRole
  subst ctx; subst child
  exact .argument
private theorem SyntaxChildPorts.of_body (shape : kind=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (childRole : HEq child lamBody) :
    SyntaxChildPorts kind ctx child .body := by
  subst kind
  have hc : ctx=(Sum.inl () : Port (.op .lam)) := eq_of_heq ctxRole
  have hd : child=lamBody := eq_of_heq childRole
  subst ctx; subst child
  exact .body
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

theorem Matches.argument_child_access {t : Term} (matching : Matches g root t)
    (parent : RootAccess g root) (node : N) (ctx childPort : Port (g.label node).sort)
    (shape : (g.label node).sort=.op .app) (ctxRole : HEq ctx appCtx) (childRole : HEq childPort appArg)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
    ∃ (child : RootAccess g root) (tail : List (Endpoint g)),
      child.val=parent.val++(.inl ⟨node,childPort⟩)::tail ∧
      accessWord g child.val=accessWord g parent.val++[.arg] :=
  matching.child_access parent node ctx childPort .arg (.of_argument shape ctxRole childRole) finish

theorem Matches.body_child_access {t : Term} (matching : Matches g root t)
    (parent : RootAccess g root) (node : N) (ctx childPort : Port (g.label node).sort)
    (shape : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam))) (childRole : HEq childPort lamBody)
    (finish : parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩))) :
    ∃ (child : RootAccess g root) (tail : List (Endpoint g)),
      child.val=parent.val++(.inl ⟨node,childPort⟩)::tail ∧
      accessWord g child.val=accessWord g parent.val++[.body] :=
  matching.child_access parent node ctx childPort .body (.of_body shape ctxRole childRole) finish
end

end Lamping.AG


