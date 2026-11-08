import Lamping.Lamping.ExpandedPrefixClosure
namespace Lamping.Checks.Phase5Review.PrefixCounter
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
#print axioms full_generated
#print axioms cut_not_generated
end Lamping.Checks.Phase5Review.PrefixCounter




