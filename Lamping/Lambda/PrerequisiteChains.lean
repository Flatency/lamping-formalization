import Lamping.Lambda.SourceBinderOccurrences

namespace Lamping.Lambda.Labelled

/-- An occurrence edge can be used by a prerequisite chain when it is a
function edge, or the incoming context edge of a lambda. This is deliberately
not a definition of AG's auxiliary edges. -/
def PrerequisiteEligible (t : LTerm) (edge : Path) : Prop :=
  (∃ parent stamp fn arg, edge=parent++[.fn] ∧
    t.subterm parent=some (.app stamp fn arg)) ∨
  (∃ stamp body, t.subterm edge=some (.lam stamp body))

/-- The occurrence of the unique redex edge at which a chain stops. -/
def PrerequisiteRedexEdge (t : LTerm) (edge : Path) : Prop :=
  ∃ parent appStamp lamStamp body arg, edge=parent++[.fn] ∧
    t.subterm parent=some (.app appStamp (.lam lamStamp body) arg)

/-- Def.5.5.1 as finite literal occurrence paths, read from the selected node
back towards its prerequisite redex. A variable jumps to its actual lexical
lambda, without adding an edge. No successful empty chain or general path
completion is postulated. -/
inductive PrerequisiteChain (t : LTerm) : Path → List Path → Prop where
  | redex_app (lookup : t.subterm p=some (.app appStamp (.lam lamStamp body) arg)) :
      PrerequisiteChain t p [p++[.fn]]
  | redex_lam (lookup : t.subterm p=some (.app appStamp (.lam lamStamp body) arg)) :
      PrerequisiteChain t (p++[.fn]) [p++[.fn]]
  | app (lookup : t.subterm p=some (.app stamp fn arg))
      (notLambda : ∀ l b, fn≠.lam l b)
      (tail : PrerequisiteChain t (p++[.fn]) edges) :
      PrerequisiteChain t p ((p++[.fn])::edges)
  | lam (lookup : t.subterm (parent++[step])=some (.lam stamp body))
      (notFunction : step≠.fn)
      (tail : PrerequisiteChain t parent edges) :
      PrerequisiteChain t (parent++[step]) ((parent++[step])::edges)
  | var (lookup : t.subterm leaf=some (.var stamp index))
      (binder : t.subterm parent=some (.lam origin body))
      (split : leaf=parent++(.body::rest)) (depth : index=binderDepth rest)
      (tail : PrerequisiteChain t parent edges) :
      PrerequisiteChain t leaf edges

theorem PrerequisiteChain.nonempty (chain : PrerequisiteChain t p edges) : edges≠[] := by
  induction chain with
  | redex_app => simp
  | redex_lam => simp
  | app => simp
  | lam => simp
  | var _ _ _ _ _ ih => exact ih

theorem PrerequisiteChain.last_redex (chain : PrerequisiteChain t p edges) :
    ∃ edge,edges.getLast?=some edge ∧ PrerequisiteRedexEdge t edge := by
  induction chain with
  | @redex_app p a l b arg lookup => exact ⟨_,rfl,p,a,l,b,arg,rfl,lookup⟩
  | @redex_lam p a l b arg lookup => exact ⟨_,rfl,p,a,l,b,arg,rfl,lookup⟩
  | @app p a fn arg es lookup notLambda tail ih =>
    obtain ⟨edge,last,redex⟩ := ih
    cases es with
    | nil => cases tail.nonempty rfl
    | cons first rest => exact ⟨edge,by simpa only [List.getLast?_cons_cons] using last,redex⟩
  | @lam parent step a body es lookup notFunction tail ih =>
    obtain ⟨edge,last,redex⟩ := ih
    cases es with
    | nil => cases tail.nonempty rfl
    | cons first rest => exact ⟨edge,by simpa only [List.getLast?_cons_cons] using last,redex⟩
  | var _ _ _ _ _ ih => exact ih

theorem PrerequisiteChain.eligible (chain : PrerequisiteChain t p edges)
    (member : edge∈edges) : PrerequisiteEligible t edge := by
  induction chain with
  | @redex_app p a l b arg lookup =>
    have equal : edge=p++[.fn] := by simpa only [List.mem_singleton] using member
    subst edge
    exact .inl ⟨p,a,.lam l b,arg,rfl,lookup⟩
  | @redex_lam p a l b arg lookup =>
    have equal : edge=p++[.fn] := by simpa only [List.mem_singleton] using member
    subst edge
    exact .inl ⟨p,a,.lam l b,arg,rfl,lookup⟩
  | @app p a fn arg es lookup _ tail ih =>
    rcases List.mem_cons.mp member with equal | below
    · subst edge; exact .inl ⟨p,a,fn,arg,rfl,lookup⟩
    · exact ih below
  | @lam parent step a body es lookup _ tail ih =>
    rcases List.mem_cons.mp member with equal | below
    · subst edge; exact .inr ⟨a,body,lookup⟩
    · exact ih below
  | var _ _ _ _ _ ih => exact ih member

end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem append_singleton_injective {p q : Path} {s u : Step}
    (same : p++[s]=q++[u]) : p=q ∧ s=u := by
  have reversed := congrArg List.reverse same
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.cons_append] at reversed
  have parts := List.cons.inj reversed
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩

private theorem app_not_redex {t : LTerm}
    (lookup : t.subterm p=some (.app stamp fn arg))
    (notLambda : ∀ l b,fn≠.lam l b) : ¬PrerequisiteRedexEdge t (p++[.fn]) := by
  rintro ⟨other,a,l,b,argument,equal,atOther⟩
  have parents := (append_singleton_injective equal).1
  subst other
  have terms := Option.some.inj (lookup.symm.trans atOther)
  have functions := LTerm.app.inj terms |>.2.1
  exact notLambda l b functions

private theorem lam_not_redex {t : LTerm} (notFunction : step≠.fn) :
    ¬PrerequisiteRedexEdge t (parent++[step]) := by
  rintro ⟨other,a,l,b,argument,equal,_⟩
  exact notFunction (append_singleton_injective equal).2

 theorem PrerequisiteChain.redex_only_last (chain : PrerequisiteChain t p edges) :
    ∃ before last,edges=before++[last] ∧ PrerequisiteRedexEdge t last ∧
      ∀ edge∈before,¬PrerequisiteRedexEdge t edge := by
  induction chain with
  | @redex_app p a l b arg lookup =>
    exact ⟨[],p++[.fn],rfl,⟨p,a,l,b,arg,rfl,lookup⟩,by simp⟩
  | @redex_lam p a l b arg lookup =>
    exact ⟨[],p++[.fn],rfl,⟨p,a,l,b,arg,rfl,lookup⟩,by simp⟩
  | @app p a fn arg es lookup notLambda tail ih =>
    obtain ⟨before,last,equal,redex,notRedex⟩ := ih
    refine ⟨(p++[.fn])::before,last,by simp only [List.cons_append,equal],redex,?_⟩
    intro edge member
    rcases List.mem_cons.mp member with same | below
    · subst edge; exact app_not_redex lookup notLambda
    · exact notRedex edge below
  | @lam parent step a body es lookup notFunction tail ih =>
    obtain ⟨before,last,equal,redex,notRedex⟩ := ih
    refine ⟨(parent++[step])::before,last,by simp only [List.cons_append,equal],redex,?_⟩
    intro edge member
    rcases List.mem_cons.mp member with same | below
    · subst edge; exact lam_not_redex notFunction
    · exact notRedex edge below
  | var _ _ _ _ _ ih => exact ih
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem lambda_child {t : LTerm}
    (lookup : t.subterm p=some (.app a (.lam l b) arg)) :
    t.subterm (p++[.fn])=some (.lam l b) := by
  rw [LTerm.subterm_append,lookup]; rfl

 theorem PrerequisiteChain.app_cases (chain : PrerequisiteChain t p edges)
    (atApp : t.subterm p=some (.app a fn arg)) :
    (∃ l b,fn=.lam l b ∧ edges=[p++[.fn]]) ∨
    (∀ l b,fn≠.lam l b) ∧ ∃ tail,edges=(p++[.fn])::tail ∧
      PrerequisiteChain t (p++[.fn]) tail := by
  cases chain with
  | redex_app lookup =>
    have same := LTerm.app.inj (Option.some.inj (atApp.symm.trans lookup))
    exact .inl ⟨_,_,same.2.1,rfl⟩
  | redex_lam lookup =>
    have impossible := Option.some.inj (atApp.symm.trans (lambda_child lookup))
    cases impossible
  | app lookup notLambda tail =>
    have same := LTerm.app.inj (Option.some.inj (atApp.symm.trans lookup))
    cases same.2.1
    exact .inr ⟨notLambda,_,rfl,tail⟩
  | lam lookup _ _ => cases Option.some.inj (atApp.symm.trans lookup)
  | var lookup _ _ _ _ => cases Option.some.inj (atApp.symm.trans lookup)

 theorem PrerequisiteChain.lambda_cases (chain : PrerequisiteChain t p edges)
    (atLambda : t.subterm p=some (.lam a body)) :
    (∃ parent appStamp arg,p=parent++[.fn] ∧
      t.subterm parent=some (.app appStamp (.lam a body) arg) ∧edges=[p]) ∨
    ∃ parent step tail,p=parent++[step] ∧ step≠.fn ∧edges=p::tail ∧
      PrerequisiteChain t parent tail := by
  cases chain with
  | redex_app lookup => cases Option.some.inj (atLambda.symm.trans lookup)
  | redex_lam lookup =>
    have same := LTerm.lam.inj (Option.some.inj (atLambda.symm.trans (lambda_child lookup)))
    cases same.1
    cases same.2
    exact .inl ⟨_,_,_,rfl,lookup,rfl⟩
  | app lookup _ _ => cases Option.some.inj (atLambda.symm.trans lookup)
  | lam _ notFunction tail => exact .inr ⟨_,_,_,rfl,notFunction,rfl,tail⟩
  | var lookup _ _ _ _ => cases Option.some.inj (atLambda.symm.trans lookup)

 theorem PrerequisiteChain.variable_cases (chain : PrerequisiteChain t p edges)
    (atVar : t.subterm p=some (.var a index)) :
    ∃ parent rest origin body,p=parent++(.body::rest) ∧index=binderDepth rest ∧
      t.subterm parent=some (.lam origin body) ∧PrerequisiteChain t parent edges := by
  cases chain with
  | redex_app lookup => cases Option.some.inj (atVar.symm.trans lookup)
  | redex_lam lookup => cases Option.some.inj (atVar.symm.trans (lambda_child lookup))
  | app lookup _ _ => cases Option.some.inj (atVar.symm.trans lookup)
  | lam lookup _ _ => cases Option.some.inj (atVar.symm.trans lookup)
  | var lookup binder split depth tail =>
    have same := LTerm.var.inj (Option.some.inj (atVar.symm.trans lookup))
    cases same.2
    exact ⟨_,_,_,_,split,depth,binder,tail⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem same_last_step {p q : Path} {s u : Step}
    (same : p++[s]=q++[u]) : p=q ∧ s=u := by
  have reversed := congrArg List.reverse same
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.cons_append] at reversed
  have parts := List.cons.inj reversed
  exact ⟨by simpa only [List.reverse_reverse] using congrArg List.reverse parts.2,parts.1⟩

 theorem PrerequisiteChain.unique (chain : PrerequisiteChain t p edges)
    (other : PrerequisiteChain t p more) : edges=more := by
  induction chain generalizing more with
  | @redex_app p a l b arg lookup =>
    rcases other.app_cases lookup with ⟨_,_,_,equal⟩ | ⟨notLambda,_⟩
    · exact equal.symm
    · exact False.elim (notLambda l b rfl)
  | @redex_lam p a l b arg lookup =>
    rcases other.lambda_cases (lambda_child lookup) with ⟨_,_,_,_,_,equal⟩ |
      ⟨parent,step,tail,equal,notFunction,_,_⟩
    · exact equal.symm
    · exact False.elim (notFunction (same_last_step equal).2.symm)
  | @app p a fn arg es lookup notLambda tail ih =>
    rcases other.app_cases lookup with ⟨l,b,equal,_⟩ | ⟨_,rest,equal,restChain⟩
    · exact False.elim (notLambda l b equal)
    · rw [equal,ih restChain]
  | @lam parent step a body es lookup notFunction tail ih =>
    rcases other.lambda_cases lookup with ⟨_,_,_,equal,_,_⟩ |
      ⟨otherParent,otherStep,rest,equal,_,listEq,restChain⟩
    · exact False.elim (notFunction (same_last_step equal).2)
    · have same := same_last_step equal
      cases same.1
      rw [listEq,ih restChain]
  | @var leaf a index parent origin body rest es lookup binder split depth tail ih =>
    obtain ⟨otherParent,otherRest,_,_,otherSplit,otherDepth,_,restChain⟩ :=
      other.variable_cases lookup
    have same := binding_prefix_depth_unique (split.symm.trans otherSplit) (depth.symm.trans otherDepth)
    cases same.1
    exact ih restChain
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled

/-- Auxiliary syntax edge, with the explicitly user-approved AND correction
of AG print140/PDF142: neither a function departure nor a lambda context
arrival. This definition alone asserts no physical separation invariant. -/
def AuxiliaryAt (t : LTerm) (edge : Path) : Prop :=
  ¬(∃ parent stamp fn arg,edge=parent++[.fn] ∧
    t.subterm parent=some (.app stamp fn arg)) ∧
  ¬(∃ stamp body,t.subterm edge=some (.lam stamp body))

theorem auxiliaryAt_iff_not_eligible : AuxiliaryAt t edge ↔ ¬PrerequisiteEligible t edge := by
  simp only [AuxiliaryAt,PrerequisiteEligible,not_or]

theorem PrerequisiteChain.not_auxiliary (chain : PrerequisiteChain t p edges)
    (member : edge∈edges) : ¬AuxiliaryAt t edge := by
  intro auxiliary
  exact (auxiliaryAt_iff_not_eligible.mp auxiliary) (chain.eligible member)

end Lamping.Lambda.Labelled