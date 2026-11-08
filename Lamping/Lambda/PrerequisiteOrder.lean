import Lamping.Lambda.PrerequisiteChains

namespace Lamping.Lambda.Labelled

/-- Size counts syntax occurrences, independently of repeated labels. -/
def prerequisiteNodeCount : LTerm → Nat
  | .var _ _ => 1
  | .lam _ body => 1+prerequisiteNodeCount body
  | .app _ fn arg => prerequisiteNodeCount fn+1+prerequisiteNodeCount arg

/-- Function subtree, application, argument subtree; lambdas precede their
body. This static occurrence order is not a beta reduction measure. -/
def prerequisiteOrder : LTerm → Path → Nat
  | .var _ _,_ => 0
  | .lam _ _,[] => 0
  | .lam _ body,.body::p => 1+prerequisiteOrder body p
  | .app _ fn _,[] => prerequisiteNodeCount fn
  | .app _ fn _,.fn::p => prerequisiteOrder fn p
  | .app _ fn arg,.arg::p => prerequisiteNodeCount fn+1+prerequisiteOrder arg p
  | _,_ => 0

theorem prerequisiteOrder_root_bound (t : LTerm) :
    prerequisiteOrder t []<prerequisiteNodeCount t := by
  cases t <;> simp only [prerequisiteOrder,prerequisiteNodeCount] <;> omega

/-- Any actual subtree occupies the same order interval at every descendant.
This is occurrence-based; no INIT or label injectivity is needed. -/
theorem prerequisiteOrder_subtree (lookup : t.subterm p=some sub) :
    ∃ offset,∀ q,prerequisiteOrder t (p++q)=offset+prerequisiteOrder sub q := by
  induction p generalizing t with
  | nil =>
    have same : t=sub := Option.some.inj (by simpa only [LTerm.subterm] using lookup)
    subst sub
    exact ⟨0,fun q=>by simp⟩
  | cons step p ih =>
    cases t with
    | var stamp index => cases step <;> simp [LTerm.subterm] at lookup
    | lam stamp body =>
      cases step with
      | fn => simp [LTerm.subterm] at lookup
      | arg => simp [LTerm.subterm] at lookup
      | body =>
        obtain ⟨offset,same⟩ := ih lookup
        refine ⟨1+offset,?_⟩
        intro q
        simp only [List.cons_append,prerequisiteOrder]
        rw [same q]
        omega
    | app stamp fn arg =>
      cases step with
      | body => simp [LTerm.subterm] at lookup
      | fn =>
        obtain ⟨offset,same⟩ := ih lookup
        exact ⟨offset,fun q=>by simpa only [List.cons_append,prerequisiteOrder] using same q⟩
      | arg =>
        obtain ⟨offset,same⟩ := ih lookup
        refine ⟨prerequisiteNodeCount fn+1+offset,?_⟩
        intro q
        simp only [List.cons_append,prerequisiteOrder]
        rw [same q]
        omega

/-- A nonterminal dependency in the actual chase. The redex lambda-function
case stops instead of advancing from that lambda back to its application. -/
inductive PrerequisiteDependency (t : LTerm) : Path → Path → Prop where
  | app (lookup : t.subterm p=some (.app a fn arg))
      (notLambda : ∀ l b,fn≠.lam l b) : PrerequisiteDependency t p (p++[.fn])
  | lam (lookup : t.subterm parent=some term)
      (child : t.subterm (parent++[step])=some (.lam a body))
      (notFunction : step≠.fn) : PrerequisiteDependency t (parent++[step]) parent
  | var (lookup : t.subterm leaf=some (.var a index))
      (binder : t.subterm parent=some (.lam origin body))
      (split : leaf=parent++(.body::rest)) (depth : index=binderDepth rest) :
      PrerequisiteDependency t leaf parent

theorem PrerequisiteDependency.order_lt (dependency : PrerequisiteDependency t p q) :
    prerequisiteOrder t q<prerequisiteOrder t p := by
  cases dependency with
  | @app p a fn arg lookup notLambda =>
    obtain ⟨offset,same⟩ := prerequisiteOrder_subtree lookup
    have root := same []
    have child := same [.fn]
    simp only [List.append_nil,prerequisiteOrder] at root child
    have bound := prerequisiteOrder_root_bound fn
    omega
  | @lam parent term step a body lookup child notFunction =>
    obtain ⟨offset,same⟩ := prerequisiteOrder_subtree lookup
    have atChild : term.subterm [step]=some (.lam a body) := by
      rw [LTerm.subterm_append,lookup] at child
      exact child
    have root := same []
    have next := same [step]
    simp only [List.append_nil] at root
    cases term <;> cases step <;> simp_all [LTerm.subterm,prerequisiteOrder]
    all_goals omega
  | @var leaf a index parent origin body rest lookup binder split depth =>
    obtain ⟨offset,same⟩ := prerequisiteOrder_subtree binder
    have root := same []
    have descendant := same (.body::rest)
    simp only [List.append_nil,prerequisiteOrder] at root descendant
    rw [split]
    omega

end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled

/-- The genuine dependency chase is well founded, including variables which
jump to lexical binders. This is not deduced from finiteness of the graph. -/
theorem prerequisiteDependency_wellFounded (t : LTerm) :
    WellFounded (fun next current => PrerequisiteDependency t current next) := by
  exact Subrelation.wf (fun dependency=>dependency.order_lt)
    (InvImage.wf (prerequisiteOrder t) Nat.lt_wfRel.wf)

end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled

/-- Uniform finite bound for every successful chain at the given occurrence.
The bound follows the same strictly decreasing chase, not the proof-tree size. -/
theorem PrerequisiteChain.length_le (chain : PrerequisiteChain t p edges) :
    edges.length≤prerequisiteOrder t p+1 := by
  induction chain with
  | redex_app => simp only [List.length_cons,List.length_nil]; omega
  | redex_lam => simp only [List.length_cons,List.length_nil]; omega
  | app lookup notLambda tail ih =>
    have smaller := (PrerequisiteDependency.app lookup notLambda).order_lt
    simp only [List.length_cons]
    omega
  | @lam parent step stamp body es lookup notFunction tail ih =>
    have child := lookup
    rw [LTerm.subterm_append] at child
    cases atParent : t.subterm parent with
    | none => rw [atParent] at child; cases child
    | some term =>
      have smaller := (PrerequisiteDependency.lam atParent lookup notFunction).order_lt
      simp only [List.length_cons]
      omega
  | var lookup binder split depth tail ih =>
    have smaller := (PrerequisiteDependency.var lookup binder split depth).order_lt
    omega

end Lamping.Lambda.Labelled