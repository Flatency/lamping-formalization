import Lamping.Lamping.OrdinaryEndpointExclusion
import Lamping.Lamping.ExpandedInsertionGeometry
import Lamping.Lamping.PathSitePrincipalRoutes
namespace Lamping.AG
open Graph
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

private theorem adjacent_prefix {α : Type} (xs ys : List α) (a b : α)
    (member : (a,b)∈xs.zip xs.tail) : (a,b)∈(xs++ys).zip (xs++ys).tail := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    cases xs with
    | nil => simp at member
    | cons y xs =>
      simp only [List.cons_append,List.tail_cons,List.zip_cons_cons,List.mem_cons] at member ⊢
      exact member.elim Or.inl (fun h => Or.inr (ih h))

private theorem adjacent_last {α : Type} (xs : List α) (a b : α)
    (last : xs.getLast?=some a) : (a,b)∈(xs++[b]).zip (xs++[b]).tail := by
  induction xs with
  | nil => cases last
  | cons x xs ih =>
    cases xs with
    | nil => have same := Option.some.inj last; subst a; simp
    | cons y xs =>
      simp only [List.cons_append,List.tail_cons,List.zip_cons_cons,List.mem_cons]
      exact Or.inr (ih (by simpa only [List.getLast?_cons_cons] using last))

/-- Backward finite tracing retains the literal whole transparent suffix.
No extension of a partial path is used. -/
theorem Forward.transparent_suffix {root : B} {es : List (Endpoint g)}
    (fw : Forward g es) (rooted : es.head?=some (.inr (.inl root)))
    (route : List (Endpoint g)) (first : Endpoint g)
    (start : route.head?=some first)
    (turns : ∀ e f,(e,f)∈route.zip route.tail →
      ∃ w d,g.wire e=.inr (.inr (w,d)) ∧f=.inr (.inr (w,!d)))
    (finish : es.getLast?=route.getLast?) :
    ∃ pre,es=pre++route ∧ Forward g (pre++[first]) ∧
      (pre++[first]).head?=some (.inr (.inl root)) := by
  have nonempty : route≠[] := by intro empty; rw [empty] at start; cases start
  obtain ⟨last,atLast⟩ : ∃ last,route.getLast?=some last := by
    cases h : route.getLast? with
    | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp h))
    | some x => exact ⟨x,rfl⟩
  obtain ⟨front,decomp⟩ := List.getLast?_eq_some_iff.mp atLast
  cases front with
  | nil =>
    have same : last=first := Option.some.inj (by simpa only [decomp,List.nil_append,List.head?_cons] using start)
    subst last
    obtain ⟨pre,split⟩ := List.getLast?_eq_some_iff.mp (finish.trans atLast)
    exact ⟨pre,by simpa only [decomp,List.nil_append] using split,by simpa only [split] using fw,
      by simpa only [split] using rooted⟩
  | cons x front =>
    obtain ⟨previous,prevLast⟩ : ∃ previous,(x::front).getLast?=some previous := by
      cases h : (x::front).getLast? with
      | none => have bad := List.getLast?_eq_none_iff.mp h; cases bad
      | some y => exact ⟨y,rfl⟩
    obtain ⟨w,d,arrives,leaves⟩ := turns previous last (by rw [decomp]; exact adjacent_last _ _ _ prevLast)
    have esLast : es.getLast?=some (.inr (.inr (w,!d))) := by rw [finish,atLast,leaves]
    obtain ⟨short,split,shortFw,shortRoot,shortLast⟩ := fw.transparent_predecessor rooted w (!d) esLast
    have shortEnd : short.getLast?=(x::front).getLast? := by
      rw [shortLast,prevLast]
      simp only [Bool.not_not]
      rw [←arrives,Pairing.involutive]
    obtain ⟨pre,old,preFw,preRoot⟩ := shortFw.transparent_suffix shortRoot (x::front) first
      (by simpa only [decomp,List.cons_append,List.head?_cons] using start)
      (fun e f h => turns e f (by rw [decomp]; exact adjacent_prefix _ _ _ _ h)) shortEnd
    exact ⟨pre,by rw [split,old,decomp,leaves,List.append_assoc],preFw,preRoot⟩
termination_by route.length
decreasing_by rw [decomp]; simp

private theorem app_input {kind : Kind} {p q : Port kind} (dir : ForwardPorts kind p q)
    (sort : kind=.op .app) (role : HEq q (Sum.inl () : Port (.op .app))) : HEq p appCtx := by
  subst kind
  exact heq_of_eq dir.1

private theorem app_arrival (r : BetaEdge g) (node : N)
    (p q : Port (g.label node).sort)
    (dir : ForwardPorts (g.label node).sort p q)
    (leaves : (Sum.inl ⟨node,q⟩ : Endpoint g)=r.funEnd) :
    (Sum.inl ⟨node,p⟩ : Endpoint g)=.inl ⟨r.app,r.appCtx⟩ := by
  have nodes : node=r.app := congrArg Sigma.fst (Sum.inl.inj leaves)
  subst node
  have same : q=r.appFun := by cases Sum.inl.inj leaves; rfl
  subst q
  have dir' : HEq p appCtx := app_input dir (congrArg Label.sort r.appLabel) r.appFun_role
  have ports : p=r.appCtx := eq_of_heq (dir'.trans r.appCtx_role.symm)
  rw [ports]

private theorem Forward.app_last (r : BetaEdge g)
    (pre : List (Endpoint g)) (fw : Forward g (pre++[r.funEnd]))
    (nonempty : pre≠[]) :
    Forward g pre ∧
      pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)) := by
  induction pre with
  | nil => exact False.elim (nonempty rfl)
  | cons x pre ih =>
    cases pre with
    | nil =>
      cases fw with
      | node n p q arrival leaves direction rest =>
        have toCtx := (arrival.trans (app_arrival r n p q direction leaves.symm))
        refine ⟨.single _,?_⟩
        simp only [List.getLast?_cons,List.getLast?_nil]
        exact congrArg some ((congrArg g.wire.mate toCtx).symm.trans (Pairing.involutive g.wire x)).symm
      | transparent w d arrival leaves rest => cases leaves
    | cons y pre =>
      cases fw with
      | node n p q arrival leaves direction rest =>
        obtain ⟨old,last⟩ := ih rest (by simp)
        exact ⟨.node n p q arrival leaves direction old,
          by simpa only [List.getLast?_cons_cons] using last⟩
      | transparent w d arrival leaves rest =>
        obtain ⟨old,last⟩ := ih rest (by simp)
        exact ⟨.transparent w d arrival leaves old,
          by simpa only [List.getLast?_cons_cons] using last⟩

/-- An actual rooted forward path arriving at the lambda context must contain
the entire selected principal route, preceded by the application context.
The supplied assignment is preserved, including its final context. -/
theorem BetaEdge.principal_prefix_reflection (r : BetaEdge g) {root : B}
    {es : List (Endpoint g)} {a d : Context} (fw : Forward g es)
    (rooted : es.head?=some (.inr (.inl root)))
    (labels : Labelling g es a d)
    (finish : es.getLast?=some (g.wire r.ctxEnd)) :
    ∃ pre, es=pre++r.principal ∧
      pre.getLast?=some (g.wire (.inl ⟨r.app,r.appCtx⟩)) ∧
      pre.head?=some (.inr (.inl root)) ∧Forward g pre ∧Labelling g pre a d := by
  obtain ⟨pre,split,prefixFw,prefixRoot⟩ := fw.transparent_suffix rooted r.principal r.funEnd
    r.principalStart r.transparent (finish.trans r.principalEnd.symm)
  have nonempty : pre≠[] := by
    intro empty
    rw [empty] at prefixRoot
    cases prefixRoot
  obtain ⟨preFw,preLast⟩ := prefixFw.app_last r pre nonempty
  have preRoot : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (nonempty rfl)
    | cons x pre => exact prefixRoot
  rw [split] at labels
  obtain ⟨middle,preLabels⟩ := labels.prefix nonempty
  have stitched := preLabels.expanded.splice preLast (r.principal_labeling middle).expanded
    r.principalStart (by simpa only [Pairing.involutive] using ExpandedTurn.ordinary (r.app_fun_turn middle))
  have same : middle=d := stitched.output_unique labels.expanded
  exact ⟨pre,split,preLast,preRoot,preFw,by simpa only [same] using preLabels⟩
end
end Lamping.AG


