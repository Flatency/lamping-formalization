import Lamping.Lamping.MatchingNestedGeneratedBase
import Lamping.Lambda.ArgumentCopies
import Lamping.Lamping.PairedArgumentInsertion
import Lamping.Lamping.ReachableNesting
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
private theorem principal_prefix_labels (edge : BetaEdge g) {pre : List (Endpoint g)}
    {a b : Context} (labels : Labelling g (pre++edge.principal) a b)
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨edge.app,edge.appCtx⟩))) :
    Labelling g pre a b := by
  have nonempty : pre≠[] := by intro empty; rw [empty] at preEnd; cases preEnd
  obtain ⟨middle,prefixLabels⟩ := labels.prefix nonempty
  have extended : Labelling g (pre++edge.principal) a middle := by
    apply prefixLabels.append_seam (edge.principal_labeling middle)
    intro e f finish head
    have eEq := Option.some.inj (finish.symm.trans preEnd)
    have fEq := Option.some.inj (head.symm.trans edge.principalStart)
    rw [eEq,fEq,Pairing.involutive]
    exact edge.app_fun_turn middle
  have same := extended.output_unique labels
  exact same ▸ prefixLabels

/-- Two original nested binders supply a genuinely coherent TWO-block
insertion for every root input. All loops, common stem and the previously
inserted argument's total paired labels are constructed from source data. -/
theorem ActualRedexAccess.nested_coherent_inputs
    {t : Term} {outerRedex innerRedex : RedexOcc t}
    (outerSource : ActualRedexAccess g root outerRedex)
    (innerSource : ActualRedexAccess g root innerRedex)
    (matching : Matches g root t) (inputs : RootInputs g root)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (transparency : Transparency g root) (outer inner : BetaEdge g)
    (outerApp : outerSource.connection.app=outer.app) (outerLam : outerSource.connection.lam=outer.lam)
    (outerPrincipal : outerSource.connection.edges=outer.principal)
    (innerApp : innerSource.connection.app=inner.app) (innerLam : innerSource.connection.lam=inner.lam)
    (innerPrincipal : innerSource.connection.edges=inner.principal)
    {body argument innerBody innerArgument : Term}
    (outerLookup : subtermAt t outerRedex.val=some (.app (.lam body) argument))
    (innerLookup : subtermAt t innerRedex.val=some (.app (.lam innerBody) innerArgument))
    (y z q : Path) (argumentPosition : Position argument)
    (nestedAt : innerRedex.val=(outerRedex.val++[.fn,.body])++y)
    (outerVariable : subtermAt body (y++(.arg::z))=some (.var (binderDepth (y++(.arg::z)))))
    (innerVariable : ArgumentOccurrence innerBody q) :
    ∃ (pre loop tail suffix : List (Endpoint g)),
      innerSource.parent.val=(outerSource.parent.val++outer.principal)++pre ∧
      ∀ requested : Context,∃ output,
        CoherentExpandedCore g root
          (outerSource.parent.val++outer.principal++
            (pre++inner.principal++loop++inner.reverseRoute++[inner.argEnd]++tail)++
            outer.reverseRoute++[outer.argEnd]++suffix) requested output ∧
        BetaDetourBlocks g
          (outerSource.parent.val++outer.principal++
            (pre++inner.principal++loop++inner.reverseRoute++[inner.argEnd]++tail)++
            outer.reverseRoute++[outer.argEnd]++suffix) requested output 2 := by
  obtain ⟨outerLeaf,outerLoop,initial,a,b,outerBinding,outerLeafWord,outerLeafSplit,
    outerBinder,_outerWord,outerChildLabels⟩ :=
    outerSource.bound_body_loop matching outerLookup (y++(.arg::z)) outerVariable
  obtain ⟨innerLeaf,loop,innerInitial,c,d,innerBinding,_innerLeafWord,_innerLeafSplit,
    innerBinder,_innerWord,innerChildLabels⟩ :=
    innerSource.bound_body_loop matching innerLookup q innerVariable
  obtain ⟨arg,_leaf,_loop,suffix,_a,_b,_binding,argSplit,_bodySplit,argWord,_word,_binder,
    _argGen,_bodyGen,_inserted⟩ :=
    outerSource.generated_binding_insert_base matching outer outerApp outerLam outerPrincipal
      outerLookup (y++(.arg::z)) outerVariable
  obtain ⟨innerArg,_leafI,_loopI,innerSuffix,_c,_d,_bindingI,innerArgSplit,_bodyI,innerArgWord,
    _wordI,_binderI,_argGenI,_bodyGenI,_insertedI⟩ :=
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
    apply List.append_cancel_left (as:=outerSource.child.val)
    calc
      outerSource.child.val++outerLoop=outerLeaf.val := outerLeafSplit.symm
      _=innerSource.parent.val++(inner.argEnd::innerSuffix)++rest := by rw [leafSplit,innerArgSplit]
      _=outerSource.child.val++(pre++inner.argEnd::(innerSuffix++rest)) := by
        rw [parentSplit]; simp only [List.append_assoc,List.cons_append]
  have argLookup : subtermAt t (outerRedex.val++[.arg])=some argument := by
    simp only [subtermAt_append,outerLookup,Option.bind_some,subtermAt]
  let argPosition : Position t := ⟨(outerRedex.val++[.arg])++argumentPosition.val,by
    simpa only [subtermAt_append,argLookup,Option.bind_some] using argumentPosition.property⟩
  obtain ⟨descendant,descendantWord,_⟩ := Matches.observation g matching argPosition
  obtain ⟨argRest,descendantSplit⟩ := matching.access_prefix arg descendant argumentPosition.val (by
    simpa only [argWord] using descendantWord)
  have actualArg : descendant.val=outerSource.parent.val++outer.argEnd::(suffix++argRest) := by
    rw [descendantSplit,argSplit]; simp only [List.append_assoc,List.cons_append]
  have outerCtx := endpoint_roles (g:=g) outerApp outerSource.contextPrincipal outer.appCtx_role
  have innerCtx := endpoint_roles (g:=g) innerApp innerSource.contextPrincipal inner.appCtx_role
  have outerEnd : outerSource.parent.val.getLast?=some (g.wire (.inl ⟨outer.app,outer.appCtx⟩)) := by
    rw [←outerCtx]; exact outerSource.parentFinish
  have innerEnd : innerSource.parent.val.getLast?=some (g.wire (.inl ⟨inner.app,inner.appCtx⟩)) := by
    rw [←innerCtx]; exact innerSource.parentFinish
  have outerPrefix : Labelling g outerSource.parent.val initial a :=
    principal_prefix_labels outer (by simpa only [outerSource.split,outerPrincipal] using outerChildLabels) outerEnd
  have innerPrefix : Labelling g innerSource.parent.val innerInitial c :=
    principal_prefix_labels inner (by simpa only [innerSource.split,innerPrincipal] using innerChildLabels) innerEnd
  have nesting := balance.nesting root rootDepth
  have first := inputs.ordinary_insert_coherent_streams flow positive balance rootDepth nesting transparency
    outer outerSource.parent.val outerLoop (suffix++argRest) descendant actualArg outerBinding
    (outerBinder.trans outerLam) outerPrefix outerSource.parent.property.2.1 outerEnd
  let mixedTail := (innerSuffix++rest)++outer.reverseRoute++[outer.argEnd]++(suffix++argRest)
  have mixedArgument : ∀ requested : Context,∃ output,
      BetaDetourBlocks g (innerSource.parent.val++inner.argEnd::mixedTail) requested output 1 := by
    intro requested
    obtain ⟨output,_core,paired⟩ := first requested
    refine ⟨output,?_⟩
    simpa only [mixedTail,fullParent,loopSplit,List.append_assoc,List.cons_append,List.singleton_append] using paired
  obtain ⟨terminal,role,level,last,atTerminal,incoming⟩ := descendant.incoming_endpoint
  have argEnd : (outer.argEnd::(suffix++argRest)).getLast?=some (g.wire terminal) := by
    rw [actualArg,List.getLast?_append] at last
    cases found : (outer.argEnd::(suffix++argRest)).getLast? with
    | none => cases List.getLast?_eq_none_iff.mp found
    | some e => rw [found,Option.some_or] at last; exact last
  have mixedEnd : (inner.argEnd::mixedTail).getLast?=some (g.wire terminal) := by
    have split : inner.argEnd::mixedTail=
        (inner.argEnd::((innerSuffix++rest)++outer.reverseRoute))++(outer.argEnd::(suffix++argRest)) := by
      simp only [mixedTail,List.append_assoc,List.cons_append,List.nil_append]
    rw [split,List.getLast?_append,argEnd]; rfl
  have all := inputs.insert_into_paired_argument flow positive balance rootDepth nesting transparency
    inner innerSource.parent.val loop mixedTail 1 mixedArgument innerBinding (innerBinder.trans innerLam)
    innerPrefix innerSource.parent.property.2.1 innerEnd terminal role level mixedEnd atTerminal incoming
  refine ⟨pre,loop,innerSuffix++rest,suffix++argRest,fullParent,?_⟩
  intro requested
  obtain ⟨output,core,paired⟩ := all requested
  exact ⟨output,by simpa only [mixedTail,fullParent,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using core,
    by simpa only [mixedTail,fullParent,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using paired⟩
end
end Lamping.AG

