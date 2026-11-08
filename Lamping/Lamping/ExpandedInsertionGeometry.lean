import Lamping.Lamping.ExpandedBinderOccurrences
namespace Lamping.AG
open Graph Lambda
private theorem app_fun_by_roles {index : Nat} {kind : Kind} {p q : Port kind}
    (sort : kind=.op .app) (source : HEq p appCtx) (target : HEq q (Sum.inl () : Port (.op .app)))
    (a : Context) : Traversal index kind p q a a := by
  subst kind
  have hp : p=appCtx := eq_of_heq source
  have hq : q=.inl () := eq_of_heq target
  subst p; subst q
  exact .direct (.appFun a)
private theorem app_arg_by_roles {index : Nat} {kind : Kind} {p q : Port kind}
    (sort : kind=.op .app) (source : HEq p appCtx) (target : HEq q appArg)
    (a : Context) : Traversal index kind p q a a := by
  subst kind
  have hp : p=appCtx := eq_of_heq source
  have hq : q=appArg := eq_of_heq target
  subst p; subst q
  exact .direct (.appArg a)
private theorem lam_body_by_roles {index : Nat} {kind : Kind} {p q : Port kind}
    (sort : kind=.op .lam) (source : HEq p (Sum.inl () : Port (.op .lam))) (target : HEq q lamBody)
    (a : Context) : Traversal index kind p q a a := by
  subst kind
  have hp : p=.inl () := eq_of_heq source
  have hq : q=lamBody := eq_of_heq target
  subst p; subst q
  exact .direct (.lamBody a)
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}
 theorem BetaEdge.app_fun_turn (r : BetaEdge g) (a : Context) :
     LabelledTurn g (.inl ⟨r.app,r.appCtx⟩) r.funEnd a a :=
   .node r.app r.appCtx r.appFun (app_fun_by_roles (congrArg Label.sort r.appLabel) r.appCtx_role r.appFun_role a)
 theorem BetaEdge.app_arg_turn (r : BetaEdge g) (a : Context) :
     LabelledTurn g (.inl ⟨r.app,r.appCtx⟩) r.argEnd a a :=
   .node r.app r.appCtx r.appArg (app_arg_by_roles (congrArg Label.sort r.appLabel) r.appCtx_role r.appArg_role a)
 theorem BetaEdge.lam_body_turn (r : BetaEdge g) (a : Context) :
     LabelledTurn g r.ctxEnd (.inl ⟨r.lam,r.lamBody⟩) a a :=
   .node r.lam r.lamCtx r.lamBody (lam_body_by_roles (congrArg Label.sort r.lamLabel) r.lamCtx_role r.lamBody_role a)

 theorem BetaEdge.body_entry_labeling (r : BetaEdge g) (pre : List (Endpoint g))
     (prefixLabel : ExpandedLabelling g pre input seam)
     (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩))) :
     ExpandedLabelling g (pre++r.principal++[.inl ⟨r.lam,r.lamBody⟩]) input seam := by
  have principal := prefixLabel.splice preEnd (r.principal_labeling seam).expanded r.principalStart
    (by simpa only [Pairing.involutive] using ExpandedTurn.ordinary (r.app_fun_turn seam))
  have last : (pre++r.principal).getLast?=some (g.wire r.ctxEnd) := by
    simp only [List.getLast?_append,r.principalEnd,Option.some_or,BetaEdge.ctxEnd]
  exact principal.splice last (.single _ seam) rfl
    (by simpa only [Pairing.involutive] using ExpandedTurn.ordinary (r.lam_body_turn seam))

 theorem BetaEdge.body_with_loop_labeling (r : BetaEdge g) (pre loop : List (Endpoint g))
     (prefixLabel : ExpandedLabelling g pre input seam)
     (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)))
     (loopStart : loop.head?=some (.inl ⟨r.lam,r.lamBody⟩))
     (loopLabels : ExpandedLabelling g loop seam output) :
     ExpandedLabelling g (pre++r.principal++loop) input output := by
  have principal := prefixLabel.splice preEnd (r.principal_labeling seam).expanded r.principalStart
    (by simpa only [Pairing.involutive] using ExpandedTurn.ordinary (r.app_fun_turn seam))
  have last : (pre++r.principal).getLast?=some (g.wire r.ctxEnd) := by
    simp only [List.getLast?_append,r.principalEnd,Option.some_or,BetaEdge.ctxEnd]
  exact principal.splice last loopLabels loopStart
    (by simpa only [Pairing.involutive] using ExpandedTurn.ordinary (r.lam_body_turn seam))
/-- Recover the actual body-loop assignment from a common-root prefix and
actual body labels. This never changes the input to the full body path. -/
theorem BetaEdge.body_loop_labeling (r : BetaEdge g) (pre loop : List (Endpoint g))
    (prefixLabel : ExpandedLabelling g pre input seam)
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)))
    (loopStart : loop.head?=some (.inl ⟨r.lam,r.lamBody⟩))
    (body : ExpandedLabelling g (pre++r.principal++loop) input output) :
    ExpandedLabelling g loop seam output := by
  obtain ⟨tail,decomp⟩ := List.head?_eq_some_iff.mp loopStart
  have body' : ExpandedLabelling g ((pre++r.principal)++(.inl ⟨r.lam,r.lamBody⟩)::tail) input output := by
    simpa only [decomp,List.append_assoc] using body
  obtain ⟨actual,first,last⟩ := ExpandedLabelling.split_segment (g:=g) (pre:=pre++r.principal) body'
  have entry := r.body_entry_labeling pre prefixLabel preEnd
  have same : actual=seam := first.output_unique entry
  rw [same] at last
  rw [decomp]
  exact last

/-- Recover the context at the argument occurrence as the context at the end
of the common root prefix. The app context→argument turn is actually identity. -/
theorem BetaEdge.argument_prefix_labeling (r : BetaEdge g) (pre suffix : List (Endpoint g))
    (cs : List Context) (trace : ExpandedContextTrace g (pre++r.argEnd::suffix) cs)
    (head : cs.head?=some input) (point : cs[pre.length]?=some seam)
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩))) :
    ExpandedLabelling g pre input seam := by
  have nonempty : pre≠[] := by intro empty; rw [empty] at preEnd; cases preEnd
  obtain ⟨output,full⟩ := trace.start_labelling head
  obtain ⟨actual,first⟩ := full.prefix nonempty
  have extended : ExpandedLabelling g (pre++[r.argEnd]) input actual :=
    first.splice preEnd (.single _ actual) rfl
      (by simpa only [Pairing.involutive] using ExpandedTurn.ordinary (r.app_arg_turn actual))
  have known := trace.prefix_labels pre.length point head
  have takeEq : (pre++r.argEnd::suffix).take (pre.length+1)=pre++[r.argEnd] := by
    rw [List.take_append,List.take_of_length_le (by omega)]
    simp
  rw [takeEq] at known
  have same : actual=seam := extended.output_unique known
  simpa only [same] using first

/-- An actually relabelled argument prefix can have a different root input
from the body. Its supplied end context is the actual argument suffix input. -/
theorem BetaEdge.argument_tail_labeling (r : BetaEdge g) (pre suffix : List (Endpoint g))
    (prefixLabel : ExpandedLabelling g pre input seam)
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)))
    (argument : ExpandedLabelling g (pre++r.argEnd::suffix) input output) :
    ExpandedLabelling g (r.argEnd::suffix) seam output := by
  obtain ⟨actual,first,last⟩ := ExpandedLabelling.split_segment (g:=g) (pre:=pre) argument
  have expected : ExpandedLabelling g (pre++[r.argEnd]) input seam :=
    prefixLabel.splice preEnd (.single _ seam) rfl
      (by simpa only [Pairing.involutive] using ExpandedTurn.ordinary (r.app_arg_turn seam))
  have same : actual=seam := first.output_unique expected
  simpa only [same] using last
 theorem BetaEdge.common_root_loop_labeling (r : BetaEdge g) (pre loop suffix : List (Endpoint g))
    (cs : List Context) (trace : ExpandedContextTrace g (pre++r.argEnd::suffix) cs)
    (head : cs.head?=some input) (point : cs[pre.length]?=some seam)
    (preEnd : pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)))
    (loopStart : loop.head?=some (.inl ⟨r.lam,r.lamBody⟩))
    (body : ExpandedLabelling g (pre++r.principal++loop) input output) :
    ExpandedLabelling g loop seam output :=
  r.body_loop_labeling pre loop (r.argument_prefix_labeling pre suffix cs trace head point preEnd) preEnd loopStart body
end
end Lamping.AG




