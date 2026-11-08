import Lamping.Lamping.ChainRepresentation
import Lamping.Lambda.SyntaxIncidence
namespace Lamping.Lambda.Labelled
open SyntaxIncidence
/-- Incidence only: no primitive graph traversal is asserted. -/
inductive IncidenceChase (t : LTerm) : Vertex t → List Path → List Bool → Vertex t → Prop where
 | nil : IncidenceChase t v [] [] v
 | forward (source : Source t e v) (target : Target t e w)
     (rest : IncidenceChase t w es ds z) : IncidenceChase t v (e::es) (true::ds) z
 | backward (target : Target t e v) (source : Source t e w)
     (rest : IncidenceChase t w es ds z) : IncidenceChase t v (e::es) (false::ds) z

private theorem incoming_lambda_parent
    (lookup : t.subterm (p++[s])=some (.lam a body)) :
    ∃ vertex : Vertex t, Source t (p++[s]) vertex ∧ Target t p vertex := by
  have actual := lookup
  rw [LTerm.subterm_append] at actual
  cases atParent : t.subterm p with
  | none => simp [atParent] at actual
  | some parent =>
    rw [atParent] at actual
    cases parent with
    | var stamp index => cases s <;> simp [LTerm.subterm] at actual
    | app stamp fn arg =>
      let vertex : ProperPosition t := ⟨p,Or.inl ⟨stamp,fn,arg,atParent⟩⟩
      refine ⟨some vertex,?_,Or.inl rfl⟩
      cases s with
      | fn => exact ⟨.fn,_,_,rfl,atParent,.fn⟩
      | arg => exact ⟨.arg,_,_,rfl,atParent,.arg⟩
      | body => simp [LTerm.subterm] at actual
    | lam stamp child =>
      let vertex : ProperPosition t := ⟨p,Or.inr ⟨stamp,child,atParent⟩⟩
      refine ⟨some vertex,?_,Or.inl rfl⟩
      cases s with
      | fn => simp [LTerm.subterm] at actual
      | arg => simp [LTerm.subterm] at actual
      | body => exact ⟨.body,_,_,rfl,atParent,.body⟩

theorem PrerequisiteReading.incidence_chase
    (closed : Closed t.erase) (reading : PrerequisiteReading t p es ds)
    (start : Target t p v) : ∃ finish, IncidenceChase t v es ds finish := by
  induction reading generalizing v with
  | @redex_app p a l body arg lookup =>
    let app : ProperPosition t := ⟨p,Or.inl ⟨a,_,arg,lookup⟩⟩
    let lam : ProperPosition t := ⟨p++[.fn],Or.inr ⟨l,body,by
      rw [LTerm.subterm_append,lookup]; rfl⟩⟩
    have eq := Target.unique start (show Target t p (some app) from Or.inl rfl)
    subst v
    exact ⟨some lam,.forward ⟨.fn,_,_,rfl,lookup,.fn⟩ (show Target t (p++[.fn]) (some lam) from Or.inl rfl) .nil⟩
  | @redex_lam p a l body arg lookup =>
    let app : ProperPosition t := ⟨p,Or.inl ⟨a,_,arg,lookup⟩⟩
    exact ⟨some app,.backward start (show Source t (p++[.fn]) (some app) from ⟨.fn,_,_,rfl,lookup,.fn⟩) .nil⟩
  | @app p a fn arg es ds lookup notLambda tail ih =>
    let app : ProperPosition t := ⟨p,Or.inl ⟨a,fn,arg,lookup⟩⟩
    have eq := Target.unique start (show Target t p (some app) from Or.inl rfl)
    subst v
    have valid : (subtermAt t.erase (p++[.fn])).isSome := by
      rw [←LTerm.erase_subterm,LTerm.subterm_append,lookup]; cases fn <;> rfl
    let child : Edge t := ⟨p++[.fn],valid⟩
    obtain ⟨finish,walk⟩ := ih (target_spec t closed child)
    exact ⟨finish,.forward ⟨.fn,_,_,rfl,lookup,.fn⟩ (target_spec t closed child) walk⟩
  | @lam parent step a body es ds lookup notFunction tail ih =>
    obtain ⟨vertex,source,target⟩ := incoming_lambda_parent lookup
    obtain ⟨finish,walk⟩ := ih target
    exact ⟨finish,.backward start source walk⟩
  | @var leaf a index parent origin body rest es ds lookup binder split depth tail ih =>
    let actualBinder : ProperPosition t := ⟨parent,Or.inr ⟨origin,body,binder⟩⟩
    have eq := Target.unique start (show Target t leaf (some actualBinder) from
      Or.inr ⟨a,index,origin,body,rest,lookup,binder,split,depth⟩)
    subst v
    exact ih (Or.inl rfl)
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
/-- A genuine syntax start supplies the initial vertex without a separate
endpoint witness. This is an incidence walk, not an ordinary labelled path. -/
theorem PrerequisiteReading.incidence_chase_at_position
    (closed : Closed t.erase) (position : SyntaxIncidence.Edge t)
    (reading : PrerequisiteReading t position.val es ds) :
    ∃ finish, IncidenceChase t (SyntaxIncidence.target t closed position) es ds finish :=
  reading.incidence_chase closed (SyntaxIncidence.target_spec t closed position)
end Lamping.Lambda.Labelled