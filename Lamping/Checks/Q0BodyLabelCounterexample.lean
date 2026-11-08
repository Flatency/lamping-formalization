import Lamping.Lambda.LabelHistories

namespace Lamping.Checks.Q0BodyLabelCounterexample
open Lambda Lambda.Labelled

abbrev I : Term := .lam (.var 0)
abbrev L : Term := .lam (.app (.app (.lam (.app (.var 1) (.var 0))) I) I)
abbrev bare : Term := .app (.lam (.app (.app (.var 0) I) (.app (.var 0) I))) L
abbrev original : LTerm := initLabels bare

def rootContract : LTerm → LTerm
  | .app beta (.lam alpha body) argument => LTerm.contract beta alpha body argument
  | t => t
def atPath : Path → LTerm → LTerm
  | [], t => rootContract t
  | .fn::p, .app l f a => .app l (atPath p f) a
  | .arg::p, .app l f a => .app l f (atPath p a)
  | .body::p, .lam l b => .lam l (atPath p b)
  | _, t => t

abbrev t1 := atPath [] original
abbrev t2 := atPath [.fn] t1
abbrev t3 := atPath [.arg] t2
abbrev t4 := atPath [.fn,.fn,.fn,.body] t3
abbrev target := atPath [.arg,.fn,.fn,.body] t4
abbrev schedule : List Path := [[],[.fn],[.arg],[.fn,.fn,.fn,.body],[.arg,.fn,.fn,.body]]
abbrev left : Path := [.fn,.fn,.fn]
abbrev right : Path := [.arg,.fn,.fn]
abbrev a : Label := ((Label.atom 4).concat (Label.atom 1).under).concat (.atom 11)
abbrev b : Label := ((Label.atom 8).concat (Label.atom 1).under).concat (.atom 11)
abbrev c : Label := ((Label.atom 16).concat a.under).concat (.atom 5)
abbrev d : Label := ((Label.atom 16).concat b.under).concat (.atom 9)
abbrev gamma : Label := ((((Label.atom 15).concat c.over).concat (.atom 6)).concat c.under).concat (.atom 17)
abbrev delta : Label := ((((Label.atom 15).concat d.over).concat (.atom 10)).concat d.under).concat (.atom 17)

def actualHistory : History schedule original target :=
  .cons (.root _ _ _ _)
    (.cons (.fn (.root _ _ _ _))
      (.cons (.arg (.root _ _ _ _))
        (.cons (.fn (.fn (.fn (.body (.root _ _ _ _)))))
          (.cons (.arg (.fn (.fn (.body (.root _ _ _ _))))) (.nil _)))))

theorem actual_initial : INIT original ∧ Closed original.erase ∧ nodeCount bare = 22 :=
  ⟨init_is_INIT _, by change Scoped 0 bare; simp [Scoped], rfl⟩

theorem actual_two_function_lambdas :
    target.subterm left = some (.lam (.atom 14) (.var gamma 0)) ∧
    target.subterm right = some (.lam (.atom 14) (.var delta 0)) ∧
    target.degreeAt [.fn,.fn] = some (.atom 14) ∧
    target.degreeAt [.arg,.fn] = some (.atom 14) := ⟨rfl,rfl,rfl,rfl⟩

theorem actual_body_labels_differ : gamma ≠ delta := by decide

theorem actual_generic_body_label_counterexample :
    INIT original ∧ Closed original.erase ∧ History schedule original target ∧
    target.subterm left = some (.lam (.atom 14) (.var gamma 0)) ∧
    target.subterm right = some (.lam (.atom 14) (.var delta 0)) ∧ gamma ≠ delta :=
  ⟨actual_initial.1,actual_initial.2.1,actualHistory,
    actual_two_function_lambdas.1,actual_two_function_lambdas.2.1,actual_body_labels_differ⟩

#print axioms actual_initial
#print axioms actualHistory
#print axioms actual_two_function_lambdas
#print axioms actual_body_labels_differ
#print axioms actual_generic_body_label_counterexample

end Lamping.Checks.Q0BodyLabelCounterexample
