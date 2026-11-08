import Lamping.Lamping.MatchingBetaGeneratedBase
import Lamping.Lamping.GeneratedNestedInsert
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
private theorem endpoint_roles {T : Type} {canonical : T} {n m : N}
    {p : Port (g.label n).sort} {q : Port (g.label m).sort}
    (nodes : n=m) (left : HEq p canonical) (right : HEq q canonical) :
    (.inl ⟨n,p⟩ : Endpoint g)=.inl ⟨m,q⟩ := by
  subst m
  cases eq_of_heq (left.trans right.symm)
  rfl

/-- Original nested syntax supplies every intermediate premise of the
finite nested insertion, including the SAME physical root stem. No loop,
common-prefix or generated-path certificate is required from the caller. -/
theorem ActualRedexAccess.nested_generated_base
    {t : Term} {outerRedex innerRedex : RedexOcc t}
    (outerSource : ActualRedexAccess g root outerRedex)
    (innerSource : ActualRedexAccess g root innerRedex)
    (matching : Matches g root t) (outer inner : BetaEdge g)
    (outerApp : outerSource.connection.app=outer.app)
    (outerLam : outerSource.connection.lam=outer.lam)
    (outerPrincipal : outerSource.connection.edges=outer.principal)
    (innerApp : innerSource.connection.app=inner.app)
    (innerLam : innerSource.connection.lam=inner.lam)
    (innerPrincipal : innerSource.connection.edges=inner.principal)
    {body argument innerBody innerArgument : Term}
    (outerLookup : subtermAt t outerRedex.val=some (.app (.lam body) argument))
    (innerLookup : subtermAt t innerRedex.val=some (.app (.lam innerBody) innerArgument))
    (y z q : Path)
    (nestedAt : innerRedex.val=(outerRedex.val++[.fn,.body])++y)
    (outerVariable : subtermAt body (y++(.arg::z))=some (.var (binderDepth (y++(.arg::z)))))
    (innerVariable : subtermAt innerBody q=some (.var (binderDepth q))) :
    ∃ (pre loop tail suffix : List (Endpoint g)),
      innerSource.parent.val=(outerSource.parent.val++outer.principal)++pre ∧
      GeneratedExpandedBindingLoop g root (outerSource.parent.val++outer.principal) outer.lam
        (pre++inner.principal++loop++inner.reverseRoute++[inner.argEnd]++tail) ∧
      GeneratedExpandedProperPath g root
        (outerSource.parent.val++outer.principal++
          (pre++inner.principal++loop++inner.reverseRoute++[inner.argEnd]++tail)++
          outer.reverseRoute++[outer.argEnd]++suffix) := by
  obtain ⟨outerLeaf,outerLoop,initial,a,b,outerBinding,outerLeafWord,outerLeafSplit,
    outerBinder,_outerLoopWord,_outerChildLabels⟩ :=
    outerSource.bound_body_loop matching outerLookup (y++(.arg::z)) outerVariable
  have outerBodySplit : outerLeaf.val=outerSource.parent.val++outer.principal++outerLoop := by
    rw [outerLeafSplit,outerSource.split,outerPrincipal]
  have outerBodyGen : GeneratedExpandedProperPath g root
      (outerSource.parent.val++outer.principal++outerLoop) := by
    rw [←outerBodySplit]
    exact .base outerLeaf.property.1 outerLeaf.property.2.1
  obtain ⟨outerArg,_leaf,_loop,suffix,_a,_b,_binding,outerArgSplit,_bodySplit,
    _argWord,_loopWord,_binder,outerArgumentGen,_bodyGen,_inserted⟩ :=
    outerSource.generated_binding_insert_base matching outer outerApp outerLam outerPrincipal
      outerLookup (y++(.arg::z)) outerVariable
  obtain ⟨innerArg,innerLeaf,loop,innerSuffix,c,d,innerBinding,innerArgSplit,_innerBodySplit,
    innerArgWord,_innerLoopWord,innerBinder,_innerArgGen,innerBodyGen,_innerInserted⟩ :=
    innerSource.generated_binding_insert_base matching inner innerApp innerLam innerPrincipal
      innerLookup q innerVariable
  obtain ⟨pre,parentSplit⟩ := matching.access_prefix outerSource.child innerSource.parent (.body::y) (by
    rw [innerSource.parentWord,outerSource.childWord,nestedAt]
    simp only [List.append_assoc,List.cons_append,List.nil_append])
  obtain ⟨rest,leafSplit⟩ := matching.access_prefix innerArg outerLeaf z (by
    rw [outerLeafWord,innerArgWord,nestedAt]
    simp only [List.append_assoc,List.cons_append,List.nil_append])
  have fullParent : innerSource.parent.val=(outerSource.parent.val++outer.principal)++pre := by
    rw [parentSplit,outerSource.split,outerPrincipal]
  have loopSplit : outerLoop=pre++inner.argEnd::(innerSuffix++rest) := by
    apply List.append_cancel_left (as:=outerSource.parent.val++outer.principal)
    calc
      (outerSource.parent.val++outer.principal)++outerLoop=outerLeaf.val := outerBodySplit.symm
      _=innerSource.parent.val++(inner.argEnd::innerSuffix)++rest := by rw [leafSplit,innerArgSplit]
      _=(outerSource.parent.val++outer.principal)++(pre++inner.argEnd::(innerSuffix++rest)) := by
        rw [fullParent]
        simp only [List.append_assoc,List.cons_append]
  cases loopSplit
  have outerBinderBeta : outerBinding.binder=outer.lam := outerBinder.trans outerLam
  have ctxOuter := endpoint_roles (g:=g) outerApp outerSource.contextPrincipal outer.appCtx_role
  have ctxInner := endpoint_roles (g:=g) innerApp innerSource.contextPrincipal inner.appCtx_role
  have stemEnd : outerSource.parent.val.getLast?=some (g.wire (.inl ⟨outer.app,outer.appCtx⟩)) := by
    rw [←ctxOuter]
    exact outerSource.parentFinish
  have preNonempty : pre≠[] := by
    intro empty
    have same : innerSource.parent.val=outerSource.child.val := by simpa only [empty,List.append_nil] using parentSplit
    have word := congrArg (accessWord g) same
    rw [innerSource.parentWord,outerSource.childWord,nestedAt] at word
    have lengths := congrArg List.length word
    simp only [List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  have preEnd : pre.getLast?=some (g.wire (.inl ⟨inner.app,inner.appCtx⟩)) := by
    have finish := innerSource.parentFinish
    rw [ctxInner,parentSplit] at finish
    simpa only [List.getLast?_append,List.getLast?_eq_some_getLast preNonempty,Option.some_or] using finish
  have outerBody := endpoint_roles (g:=g) outerBinderBeta outerBinding.body_role outer.lamBody_role
  have outerBind := endpoint_roles (g:=g) outerBinderBeta outerBinding.bind_role outer.lamBind_role
  have innerBodyEnd := endpoint_roles (g:=g) innerBinder innerBinding.body_role inner.lamBody_role
  have innerBindEnd := endpoint_roles (g:=g) innerBinder innerBinding.bind_role inner.lamBind_role
  have outerStart := outerBinding.start.trans (congrArg some outerBody)
  have outerEnd := outerBinding.finish.trans (congrArg (fun e => some (g.wire e)) outerBind)
  have innerStart := innerBinding.start.trans (congrArg some innerBodyEnd)
  have innerEnd := innerBinding.finish.trans (congrArg (fun e => some (g.wire e)) innerBindEnd)
  have reducedBody : GeneratedExpandedProperPath g root
      (outerSource.parent.val++outer.principal++(pre++inner.argEnd::(innerSuffix++rest))) := by
    exact outerBodyGen
  have nestedBody : GeneratedExpandedProperPath g root
      ((outerSource.parent.val++outer.principal++pre)++inner.principal++loop) := by
    simpa only [fullParent] using innerBodyGen
  refine ⟨pre,loop,innerSuffix++rest,suffix,fullParent,?_,?_⟩
  · have outerBase := GeneratedExpandedBindingLoop.base (g:=g) (root:=root)
      (outerSource.parent.val++outer.principal) _ a b outerBinding
    have innerBase := GeneratedExpandedBindingLoop.base (g:=g) (root:=root)
      ((outerSource.parent.val++outer.principal)++pre++inner.principal) loop c d innerBinding
    rw [outerBinderBeta] at outerBase
    rw [innerBinder] at innerBase
    exact .insert (outerSource.parent.val++outer.principal) outer.lam inner pre loop (innerSuffix++rest)
      outerBase innerBase (by simpa only [List.append_assoc] using nestedBody) preEnd innerStart innerEnd
  · exact GeneratedExpandedProperPath.nested_insert outer inner outerSource.parent.val pre loop
      (innerSuffix++rest) suffix a b c d outerBinding innerBinding outerBinderBeta innerBinder
      stemEnd outerStart outerEnd preEnd innerStart innerEnd outerArgumentGen reducedBody nestedBody
end
end Lamping.AG


