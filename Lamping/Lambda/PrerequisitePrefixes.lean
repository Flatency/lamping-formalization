import Lamping.Lambda.PrerequisiteChains
namespace Lamping.Lambda.Labelled
/-- A finite actual dependency segment. Its endpoint need not have a chain;
variable jumps have no edge but preserve their exact binder coordinates. -/
inductive PrerequisitePrefix (t : LTerm) : Path → List Path → Path → Prop where
  | refl : PrerequisitePrefix t p [] p
  | app (lookup : t.subterm p=some (.app stamp fn arg))
      (notLambda : ∀ l b,fn≠.lam l b)
      (tail : PrerequisitePrefix t (p++[.fn]) edges finish) :
      PrerequisitePrefix t p ((p++[.fn])::edges) finish
  | lam (lookup : t.subterm (parent++[step])=some (.lam stamp body))
      (notFunction : step≠.fn)
      (tail : PrerequisitePrefix t parent edges finish) :
      PrerequisitePrefix t (parent++[step]) ((parent++[step])::edges) finish
  | var (lookup : t.subterm leaf=some (.var stamp index))
      (binder : t.subterm parent=some (.lam origin body))
      (split : leaf=parent++(.body::rest)) (depth : index=binderDepth rest)
      (tail : PrerequisitePrefix t parent edges finish) :
      PrerequisitePrefix t leaf edges finish

theorem PrerequisitePrefix.close (segment : PrerequisitePrefix t start edges finish)
    (tail : PrerequisiteChain t finish more) : PrerequisiteChain t start (edges++more) := by
  induction segment with
  | refl => exact tail
  | app lookup notLambda _ ih => exact .app lookup notLambda (ih tail)
  | lam lookup notFunction _ ih => exact .lam lookup notFunction (ih tail)
  | var lookup binder split depth _ ih => exact .var lookup binder split depth (ih tail)

theorem PrerequisitePrefix.append (segment : PrerequisitePrefix t start edges finish)
    (tail : PrerequisitePrefix t finish more last) :
    PrerequisitePrefix t start (edges++more) last := by
  induction segment with
  | refl => exact tail
  | app lookup notLambda _ ih => exact .app lookup notLambda (ih tail)
  | lam lookup notFunction _ ih => exact .lam lookup notFunction (ih tail)
  | var lookup binder split depth _ ih => exact .var lookup binder split depth (ih tail)

/-- The actual proper occurrence at which the next edge is read, before
any subsequent zero-edge variable jumps. -/
def PrerequisiteReads (t : LTerm) (start edge : Path) : Prop :=
  (∃ stamp fn arg,t.subterm start=some (.app stamp fn arg) ∧edge=start++[.fn]) ∨
  (∃ stamp body,t.subterm start=some (.lam stamp body) ∧edge=start)

/-- Membership in the supplied actual chain constructs the finite segment,
its exact remaining chain, and its actual next app/lambda occurrence. -/
theorem PrerequisiteChain.split_at_member (chain : PrerequisiteChain t start edges)
    (member : edge∈edges) :
    ∃ before after middle,edges=before++(edge::after) ∧
      PrerequisitePrefix t start before middle ∧
      PrerequisiteChain t middle (edge::after) ∧PrerequisiteReads t middle edge := by
  induction chain with
  | @redex_app p a l b arg lookup =>
    have equal : edge=p++[.fn] := by simpa only [List.mem_singleton] using member
    subst edge
    exact ⟨[],[],p,rfl,.refl,.redex_app lookup,Or.inl ⟨a,.lam l b,arg,lookup,rfl⟩⟩
  | @redex_lam p a l b arg lookup =>
    have equal : edge=p++[.fn] := by simpa only [List.mem_singleton] using member
    subst edge
    refine ⟨[],[],p++[.fn],rfl,.refl,.redex_lam lookup,Or.inr ⟨l,b,?_,rfl⟩⟩
    rw [LTerm.subterm_append,lookup]; rfl
  | @app p a fn arg es lookup notLambda tail ih =>
    rcases List.mem_cons.mp member with equal | below
    · subst edge
      exact ⟨[],es,p,rfl,.refl,.app lookup notLambda tail,Or.inl ⟨a,fn,arg,lookup,rfl⟩⟩
    · obtain ⟨before,after,middle,split,segment,remainder,reads⟩ := ih below
      exact ⟨(p++[.fn])::before,after,middle,by rw [split]; rfl,
        .app lookup notLambda segment,remainder,reads⟩
  | @lam parent step a body es lookup notFunction tail ih =>
    rcases List.mem_cons.mp member with equal | below
    · subst edge
      exact ⟨[],es,parent++[step],rfl,.refl,.lam lookup notFunction tail,
        Or.inr ⟨a,body,lookup,rfl⟩⟩
    · obtain ⟨before,after,middle,split,segment,remainder,reads⟩ := ih below
      exact ⟨(parent++[step])::before,after,middle,by rw [split]; rfl,
        .lam lookup notFunction segment,remainder,reads⟩
  | var lookup binder split depth tail ih =>
    obtain ⟨before,after,middle,equal,segment,remainder,reads⟩ := ih member
    exact ⟨before,after,middle,equal,.var lookup binder split depth segment,remainder,reads⟩
end Lamping.Lambda.Labelled


