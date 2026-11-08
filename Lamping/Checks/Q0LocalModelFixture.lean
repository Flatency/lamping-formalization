import Lamping.Checks.Q0CompleteBodyLabelCounterexample
import Lamping.Lamping.InitialPathRelabelling
import Lamping.Lamping.RootObservationCoverage
import Lamping.Lamping.IndexedLevelBalance

namespace Lamping.Checks.Q0LocalModelFixture
open AG Graph Lambda Lambda.Labelled

inductive Node where
  | R | C0 | F | A | B | L | C1 | J | CJ | K | CK
  deriving DecidableEq
instance : FiniteNames Node where
  all := [.R,.C0,.F,.A,.B,.L,.C1,.J,.CJ,.K,.CK]
  complete := by intro n; cases n <;> simp

def nodeLabel : Node → Graph.Label signature
  | .R => AG.label .app 0
  | .C0 => AG.label .cro 0
  | .F => AG.label .fan 0
  | .A => AG.label .app 1
  | .B => AG.label .app 1
  | .L => AG.label .lam 1
  | .C1 => AG.label .cro 1
  | .J => AG.label .lam 2
  | .CJ => AG.label .cro 2
  | .K => AG.label .lam 2
  | .CK => AG.label .cro 2

abbrev ModelEnd := End signature Node Unit Empty nodeLabel

def mate : ModelEnd → ModelEnd
  | .inr (.inl ()) => .inl ⟨.R, .inr false⟩
  | .inl ⟨.R, .inr false⟩ => .inr (.inl ())
  | .inl ⟨.R, .inl ()⟩ => .inl ⟨.C0, .inr ()⟩
  | .inl ⟨.C0, .inr ()⟩ => .inl ⟨.R, .inl ()⟩
  | .inl ⟨.C0, .inl ()⟩ => .inl ⟨.F, .inr false⟩
  | .inl ⟨.F, .inr false⟩ => .inl ⟨.C0, .inl ()⟩
  | .inl ⟨.R, .inr true⟩ => .inl ⟨.F, .inr true⟩
  | .inl ⟨.F, .inr true⟩ => .inl ⟨.R, .inr true⟩
  | .inl ⟨.F, .inl ()⟩ => .inl ⟨.A, .inr false⟩
  | .inl ⟨.A, .inr false⟩ => .inl ⟨.F, .inl ()⟩
  | .inl ⟨.A, .inl ()⟩ => .inl ⟨.B, .inr false⟩
  | .inl ⟨.B, .inr false⟩ => .inl ⟨.A, .inl ()⟩
  | .inl ⟨.A, .inr true⟩ => .inl ⟨.K, .inl ()⟩
  | .inl ⟨.K, .inl ()⟩ => .inl ⟨.A, .inr true⟩
  | .inl ⟨.B, .inl ()⟩ => .inl ⟨.L, .inl ()⟩
  | .inl ⟨.L, .inl ()⟩ => .inl ⟨.B, .inl ()⟩
  | .inl ⟨.B, .inr true⟩ => .inl ⟨.J, .inl ()⟩
  | .inl ⟨.J, .inl ()⟩ => .inl ⟨.B, .inr true⟩
  | .inl ⟨.L, .inr true⟩ => .inl ⟨.C1, .inr ()⟩
  | .inl ⟨.C1, .inr ()⟩ => .inl ⟨.L, .inr true⟩
  | .inl ⟨.C1, .inl ()⟩ => .inl ⟨.L, .inr false⟩
  | .inl ⟨.L, .inr false⟩ => .inl ⟨.C1, .inl ()⟩
  | .inl ⟨.J, .inr true⟩ => .inl ⟨.CJ, .inr ()⟩
  | .inl ⟨.CJ, .inr ()⟩ => .inl ⟨.J, .inr true⟩
  | .inl ⟨.CJ, .inl ()⟩ => .inl ⟨.J, .inr false⟩
  | .inl ⟨.J, .inr false⟩ => .inl ⟨.CJ, .inl ()⟩
  | .inl ⟨.K, .inr true⟩ => .inl ⟨.CK, .inr ()⟩
  | .inl ⟨.CK, .inr ()⟩ => .inl ⟨.K, .inr true⟩
  | .inl ⟨.CK, .inl ()⟩ => .inl ⟨.K, .inr false⟩
  | .inl ⟨.K, .inr false⟩ => .inl ⟨.CK, .inl ()⟩
  | .inr (.inr ⟨e,_⟩) => nomatch e

def net : Net signature Node Unit Empty where
  label := nodeLabel
  wire := {
    mate := mate
    involutive := by
      rintro (⟨n,p⟩ | (u | ⟨e,d⟩))
      · cases n <;> cases p <;> rename_i x <;> cases x <;> rfl
      · cases u; rfl
      · exact nomatch e
    fixedPointFree := by
      rintro (⟨n,p⟩ | (u | ⟨e,d⟩))
      · cases n <;> cases p <;> rename_i x <;> cases x <;> intro h <;> cases h
      · cases u; intro h; cases h
      · exact nomatch e }

abbrev rootEnd : Endpoint net := .inr (.inl ())

private theorem initial_flow : FlowOn net (fun _=>true) Empty.elim := by
  rintro (⟨n,p⟩ | (u | ⟨e,d⟩))
  · cases n <;> cases p <;> rename_i x <;> cases x <;> rfl
  · cases u; rfl
  · exact nomatch e

theorem actual_rooted_initial {es : List (Endpoint net)} {a b : Context}
    (rooted : es.head?=some rootEnd) (labels : Labelling net es a b) :
    InitialLabelling (g:=net) es a b := by
  apply labels.initial_of_flow initial_flow
  intro e h
  have eq : e=rootEnd := Option.some.inj (h.symm.trans rooted)
  subst e
  rfl

theorem actual_root_inputs : RootInputs net () := by
  intro es a b terminal role level labels _forward rooted _finish _atRole _incoming requested
  obtain ⟨output,changed⟩ := (actual_rooted_initial rooted labels).relabel_input requested
  exact ⟨output,changed.labelling⟩

inductive AccessCode where

  | root | leftA | leftB | leftL | leftV | leftJ | leftJV | leftK | leftKV | rightA | rightB | rightL | rightV | rightJ | rightJV | rightK | rightKV
  deriving DecidableEq

def codes : List AccessCode := [.root,.leftA,.leftB,.leftL,.leftV,.leftJ,.leftJV,.leftK,.leftKV,.rightA,.rightB,.rightL,.rightV,.rightJ,.rightJV,.rightK,.rightKV]

def coordinate : AccessCode → Path
  | .root => []
  | .leftA => [.fn]
  | .leftB => [.fn,.fn]
  | .leftL => [.fn,.fn,.fn]
  | .leftV => [.fn,.fn,.fn,.body]
  | .leftJ => [.fn,.fn,.arg]
  | .leftJV => [.fn,.fn,.arg,.body]
  | .leftK => [.fn,.arg]
  | .leftKV => [.fn,.arg,.body]
  | .rightA => [.arg]
  | .rightB => [.arg,.fn]
  | .rightL => [.arg,.fn,.fn]
  | .rightV => [.arg,.fn,.fn,.body]
  | .rightJ => [.arg,.fn,.arg]
  | .rightJV => [.arg,.fn,.arg,.body]
  | .rightK => [.arg,.arg]
  | .rightKV => [.arg,.arg,.body]

def edges : AccessCode → List (Endpoint net)
  | .root => [rootEnd]
  | .leftA => [rootEnd,.inl ⟨.R, .inl ()⟩,.inl ⟨.C0, .inl ()⟩,.inl ⟨.F, .inl ()⟩]
  | .leftB => [rootEnd,.inl ⟨.R, .inl ()⟩,.inl ⟨.C0, .inl ()⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩]
  | .leftL => [rootEnd,.inl ⟨.R, .inl ()⟩,.inl ⟨.C0, .inl ()⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩,.inl ⟨.B, .inl ()⟩]
  | .leftV => [rootEnd,.inl ⟨.R, .inl ()⟩,.inl ⟨.C0, .inl ()⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩,.inl ⟨.B, .inl ()⟩,.inl ⟨.L, .inr true⟩,.inl ⟨.C1, .inl ()⟩]
  | .leftJ => [rootEnd,.inl ⟨.R, .inl ()⟩,.inl ⟨.C0, .inl ()⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩,.inl ⟨.B, .inr true⟩]
  | .leftJV => [rootEnd,.inl ⟨.R, .inl ()⟩,.inl ⟨.C0, .inl ()⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩,.inl ⟨.B, .inr true⟩,.inl ⟨.J, .inr true⟩,.inl ⟨.CJ, .inl ()⟩]
  | .leftK => [rootEnd,.inl ⟨.R, .inl ()⟩,.inl ⟨.C0, .inl ()⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inr true⟩]
  | .leftKV => [rootEnd,.inl ⟨.R, .inl ()⟩,.inl ⟨.C0, .inl ()⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inr true⟩,.inl ⟨.K, .inr true⟩,.inl ⟨.CK, .inl ()⟩]
  | .rightA => [rootEnd,.inl ⟨.R, .inr true⟩,.inl ⟨.F, .inl ()⟩]
  | .rightB => [rootEnd,.inl ⟨.R, .inr true⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩]
  | .rightL => [rootEnd,.inl ⟨.R, .inr true⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩,.inl ⟨.B, .inl ()⟩]
  | .rightV => [rootEnd,.inl ⟨.R, .inr true⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩,.inl ⟨.B, .inl ()⟩,.inl ⟨.L, .inr true⟩,.inl ⟨.C1, .inl ()⟩]
  | .rightJ => [rootEnd,.inl ⟨.R, .inr true⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩,.inl ⟨.B, .inr true⟩]
  | .rightJV => [rootEnd,.inl ⟨.R, .inr true⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inl ()⟩,.inl ⟨.B, .inr true⟩,.inl ⟨.J, .inr true⟩,.inl ⟨.CJ, .inl ()⟩]
  | .rightK => [rootEnd,.inl ⟨.R, .inr true⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inr true⟩]
  | .rightKV => [rootEnd,.inl ⟨.R, .inr true⟩,.inl ⟨.F, .inl ()⟩,.inl ⟨.A, .inr true⟩,.inl ⟨.K, .inr true⟩,.inl ⟨.CK, .inl ()⟩]

abbrev I : Term := .lam (.var 0)
abbrev S : Term := .app (.app I I) I
abbrev source : LTerm := Q0BodyLabelCounterexample.target
theorem source_erase : source.erase=.app S S := rfl
theorem source_closed : Closed source.erase := by change Scoped 0 (.app S S); simp [Scoped]

def termAt : AccessCode → Term
  | .root => .app S S
  | .leftA => S
  | .leftB => .app I I
  | .leftL => I
  | .leftV => .var 0
  | .leftJ => I
  | .leftJV => .var 0
  | .leftK => I
  | .leftKV => .var 0
  | .rightA => S
  | .rightB => .app I I
  | .rightL => I
  | .rightV => .var 0
  | .rightJ => I
  | .rightJV => .var 0
  | .rightK => I
  | .rightKV => .var 0

private theorem lookup_code (c : AccessCode) : subtermAt source.erase (coordinate c)=some (termAt c) := by
  cases c <;> rfl
private theorem positions_codes : positions source.erase=codes.map coordinate := rfl
private theorem code_word (c : AccessCode) : accessWord net (edges c)=coordinate c := by
  cases c <;> rfl
private theorem code_root (c : AccessCode) : (edges c).head?=some rootEnd := by
  cases c <;> rfl
private theorem code_kind (c : AccessCode) : accessKind net (edges c)=some (syntaxShape (termAt c)).kind := by
  cases c <;> rfl

def leftContext (a : Context) : Context := InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 a)
def rightContext (a : Context) : Context := InitialOffsets.fanAt 0 true a
def afterContext : AccessCode → Context → Context
  | .root,a => a
  | .leftA,a => leftContext a
  | .leftB,a => leftContext a
  | .leftL,a => leftContext a
  | .leftV,a => InitialOffsets.croAt 1 (leftContext a)
  | .leftJ,a => leftContext a
  | .leftJV,a => InitialOffsets.croAt 2 (leftContext a)
  | .leftK,a => leftContext a
  | .leftKV,a => InitialOffsets.croAt 2 (leftContext a)
  | .rightA,a => rightContext a
  | .rightB,a => rightContext a
  | .rightL,a => rightContext a
  | .rightV,a => InitialOffsets.croAt 1 (rightContext a)
  | .rightJ,a => rightContext a
  | .rightJV,a => InitialOffsets.croAt 2 (rightContext a)
  | .rightK,a => rightContext a
  | .rightKV,a => InitialOffsets.croAt 2 (rightContext a)

private theorem code_labels (c : AccessCode) (a : Context) :
    Labelling net (edges c) a (afterContext c a) := by
  cases c with
  | root => exact (.single _ _)
  | leftA => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inl ()) (.direct (.appFun (a)))) (.cons (LabelledTurn.node (g:=net) Node.C0 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 0) (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr false) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) (InitialOffsets.croAt 0 (a))))) ((.single _ _))))
  | leftB => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inl ()) (.direct (.appFun (a)))) (.cons (LabelledTurn.node (g:=net) Node.C0 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 0) (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr false) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) (InitialOffsets.croAt 0 (a))))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) ((.single _ _)))))
  | leftL => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inl ()) (.direct (.appFun (a)))) (.cons (LabelledTurn.node (g:=net) Node.C0 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 0) (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr false) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) (InitialOffsets.croAt 0 (a))))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.B (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) ((.single _ _))))))
  | leftV => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inl ()) (.direct (.appFun (a)))) (.cons (LabelledTurn.node (g:=net) Node.C0 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 0) (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr false) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) (InitialOffsets.croAt 0 (a))))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.B (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.L (.inl ()) (.inr true) (.direct (.lamBody (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.C1 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 1) (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) ((.single _ _))))))))
  | leftJ => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inl ()) (.direct (.appFun (a)))) (.cons (LabelledTurn.node (g:=net) Node.C0 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 0) (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr false) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) (InitialOffsets.croAt 0 (a))))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.B (.inr false) (.inr true) (.direct (.appArg (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) ((.single _ _))))))
  | leftJV => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inl ()) (.direct (.appFun (a)))) (.cons (LabelledTurn.node (g:=net) Node.C0 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 0) (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr false) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) (InitialOffsets.croAt 0 (a))))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.B (.inr false) (.inr true) (.direct (.appArg (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.J (.inl ()) (.inr true) (.direct (.lamBody (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.CJ (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 2) (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) ((.single _ _))))))))
  | leftK => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inl ()) (.direct (.appFun (a)))) (.cons (LabelledTurn.node (g:=net) Node.C0 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 0) (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr false) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) (InitialOffsets.croAt 0 (a))))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inr true) (.direct (.appArg (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) ((.single _ _)))))
  | leftKV => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inl ()) (.direct (.appFun (a)))) (.cons (LabelledTurn.node (g:=net) Node.C0 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 0) (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr false) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 false) (InitialOffsets.croAt 0 (a))))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inr true) (.direct (.appArg (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.K (.inl ()) (.inr true) (.direct (.lamBody (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) (.cons (LabelledTurn.node (g:=net) Node.CK (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 2) (InitialOffsets.fanAt 0 false (InitialOffsets.croAt 0 (a)))))) ((.single _ _)))))))
  | rightA => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inr true) (.direct (.appArg (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr true) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) (a)))) ((.single _ _)))
  | rightB => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inr true) (.direct (.appArg (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr true) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) (a)))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 true (a))))) ((.single _ _))))
  | rightL => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inr true) (.direct (.appArg (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr true) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) (a)))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.B (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 true (a))))) ((.single _ _)))))
  | rightV => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inr true) (.direct (.appArg (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr true) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) (a)))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.B (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.L (.inl ()) (.inr true) (.direct (.lamBody (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.C1 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 1) (InitialOffsets.fanAt 0 true (a))))) ((.single _ _)))))))
  | rightJ => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inr true) (.direct (.appArg (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr true) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) (a)))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.B (.inr false) (.inr true) (.direct (.appArg (InitialOffsets.fanAt 0 true (a))))) ((.single _ _)))))
  | rightJV => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inr true) (.direct (.appArg (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr true) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) (a)))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inl ()) (.direct (.appFun (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.B (.inr false) (.inr true) (.direct (.appArg (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.J (.inl ()) (.inr true) (.direct (.lamBody (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.CJ (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 2) (InitialOffsets.fanAt 0 true (a))))) ((.single _ _)))))))
  | rightK => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inr true) (.direct (.appArg (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr true) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) (a)))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inr true) (.direct (.appArg (InitialOffsets.fanAt 0 true (a))))) ((.single _ _))))
  | rightKV => exact .cons (LabelledTurn.node (g:=net) Node.R (.inr false) (.inr true) (.direct (.appArg (a)))) (.cons (LabelledTurn.node (g:=net) Node.F (.inr true) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.fan 0 true) (a)))) (.cons (LabelledTurn.node (g:=net) Node.A (.inr false) (.inr true) (.direct (.appArg (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.K (.inl ()) (.inr true) (.direct (.lamBody (InitialOffsets.fanAt 0 true (a))))) (.cons (LabelledTurn.node (g:=net) Node.CK (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 2) (InitialOffsets.fanAt 0 true (a))))) ((.single _ _))))))

def access (c : AccessCode) : RootAccess net () :=
  ⟨edges c,⟨⟨⟨Context.empty,afterContext c Context.empty,code_labels c _⟩,
    (actual_rooted_initial (code_root c) (code_labels c Context.empty)).forward⟩,
    code_root c,⟨_,code_kind c⟩⟩⟩

inductive LambdaCode where | L | J | K
def lambdaNode : LambdaCode → Node | .L=>.L | .J=>.J | .K=>.K
def loopEdges : LambdaCode → List (Endpoint net)
  | .L => [.inl ⟨.L,lamBody⟩,.inl ⟨.C1,.inl ()⟩]
  | .J => [.inl ⟨.J,lamBody⟩,.inl ⟨.CJ,.inl ()⟩]
  | .K => [.inl ⟨.K,lamBody⟩,.inl ⟨.CK,.inl ()⟩]
def lambdaIndex : LambdaCode → Nat | .L=>1 | .J=>2 | .K=>2

def actual_loop (code : LambdaCode) (a : Context) :
    BindingLoop net (loopEdges code) a (InitialOffsets.croAt (lambdaIndex code) a) := by
  cases code with

  | L => exact {
      binder:=.L, isLam:=rfl, body:=lamBody, bind:=lamBind,
      body_role:=HEq.rfl, bind_role:=HEq.rfl, start:=rfl, finish:=rfl,
      proper:=.cons (LabelledTurn.node (g:=net) Node.C1 (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 1) a))) (.single _ _),
      forward:=.node .C1 (.inr ()) (.inl ()) rfl rfl True.intro (.single _),
      shell:=by intro k hk; change k<1 at hk; exact (Context.replace_low a ((a.tail 1).cons .empty) hk).symm }
  | J => exact {
      binder:=.J, isLam:=rfl, body:=lamBody, bind:=lamBind,
      body_role:=HEq.rfl, bind_role:=HEq.rfl, start:=rfl, finish:=rfl,
      proper:=.cons (LabelledTurn.node (g:=net) Node.CJ (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 2) a))) (.single _ _),
      forward:=.node .CJ (.inr ()) (.inl ()) rfl rfl True.intro (.single _),
      shell:=by intro k hk; change k<2 at hk; exact (Context.replace_low a ((a.tail 2).cons .empty) hk).symm }
  | K => exact {
      binder:=.K, isLam:=rfl, body:=lamBody, bind:=lamBind,
      body_role:=HEq.rfl, bind_role:=HEq.rfl, start:=rfl, finish:=rfl,
      proper:=.cons (LabelledTurn.node (g:=net) Node.CK (.inr ()) (.inl ()) (.direct (InitialOffsets.Event.apply_rel (.cro 2) a))) (.single _ _),
      forward:=.node .CK (.inr ()) (.inl ()) rfl rfl True.intro (.single _),
      shell:=by intro k hk; change k<2 at hk; exact (Context.replace_low a ((a.tail 2).cons .empty) hk).symm }

private theorem body_departure_word (n : Node) (p : Port (net.label n).sort)
    (lam : (net.label n).sort=.op .lam) (role : HEq p lamBody) :
    arrivalWord net (.inl ⟨n,p⟩)=[.body] := by
  cases n with

  | R => cases lam
  | C0 => cases lam
  | F => cases lam
  | A => cases lam
  | B => cases lam
  | L => have same : p=lamBody := eq_of_heq role; subst p; rfl
  | C1 => cases lam
  | J => have same : p=lamBody := eq_of_heq role; subst p; rfl
  | CJ => cases lam
  | K => have same : p=lamBody := eq_of_heq role; subst p; rfl
  | CK => cases lam

private theorem suffix_index_zero {es : List (Endpoint net)}
    (bound : binderDepth (es.flatMap (arrivalWord net))≤1) {j : Nat}
    (suffix : BindingSuffix net es j) : j=0 := by
  obtain ⟨pre,loop,a,b,c,binding,_ctx,split,_ctxRole,_preEnd,_preLabels,index⟩ := suffix
  obtain ⟨tail,loopEq⟩ := List.head?_eq_some_iff.mp binding.start
  have token := body_departure_word binding.binder binding.body binding.isLam binding.body_role
  have count := bound
  rw [split,loopEq,List.flatMap_append,List.flatMap_cons,token,binderDepth_append] at count
  simp only [List.singleton_append,binderDepth] at count
  have zero : binderDepth (tail.flatMap (arrivalWord net))=0 := by omega
  have relation : j=binderDepth (tail.flatMap (arrivalWord net)) := by
    simpa only [loopEq,accessWord] using index
  exact relation.trans zero

private theorem code_body_bound (c : AccessCode) : binderDepth ((edges c).flatMap (arrivalWord net))≤1 := by
  cases c <;> decide


private theorem binding_leftV : BindingSuffix net (edges .leftV) 0 := by
  refine ⟨edges .leftL,loopEdges .L,Context.empty,afterContext .leftL Context.empty,
    afterContext .leftV Context.empty,actual_loop .L _,.inl (),rfl,HEq.rfl,rfl,code_labels .leftL _,rfl⟩

private theorem binding_leftJV : BindingSuffix net (edges .leftJV) 0 := by
  refine ⟨edges .leftJ,loopEdges .J,Context.empty,afterContext .leftJ Context.empty,
    afterContext .leftJV Context.empty,actual_loop .J _,.inl (),rfl,HEq.rfl,rfl,code_labels .leftJ _,rfl⟩

private theorem binding_leftKV : BindingSuffix net (edges .leftKV) 0 := by
  refine ⟨edges .leftK,loopEdges .K,Context.empty,afterContext .leftK Context.empty,
    afterContext .leftKV Context.empty,actual_loop .K _,.inl (),rfl,HEq.rfl,rfl,code_labels .leftK _,rfl⟩

private theorem binding_rightV : BindingSuffix net (edges .rightV) 0 := by
  refine ⟨edges .rightL,loopEdges .L,Context.empty,afterContext .rightL Context.empty,
    afterContext .rightV Context.empty,actual_loop .L _,.inl (),rfl,HEq.rfl,rfl,code_labels .rightL _,rfl⟩

private theorem binding_rightJV : BindingSuffix net (edges .rightJV) 0 := by
  refine ⟨edges .rightJ,loopEdges .J,Context.empty,afterContext .rightJ Context.empty,
    afterContext .rightJV Context.empty,actual_loop .J _,.inl (),rfl,HEq.rfl,rfl,code_labels .rightJ _,rfl⟩

private theorem binding_rightKV : BindingSuffix net (edges .rightKV) 0 := by
  refine ⟨edges .rightK,loopEdges .K,Context.empty,afterContext .rightK Context.empty,
    afterContext .rightKV Context.empty,actual_loop .K _,.inl (),rfl,HEq.rfl,rfl,code_labels .rightK _,rfl⟩

private theorem code_observes (c : AccessCode) : Observes net (edges c) (syntaxShape (termAt c)) := by
  cases c with
  | root => exact ⟨rfl,True.intro⟩
  | leftA => exact ⟨rfl,True.intro⟩
  | leftB => exact ⟨rfl,True.intro⟩
  | leftL => exact ⟨rfl,True.intro⟩
  | leftV => exact ⟨rfl,binding_leftV,fun _ h=>suffix_index_zero (code_body_bound _) h⟩
  | leftJ => exact ⟨rfl,True.intro⟩
  | leftJV => exact ⟨rfl,binding_leftJV,fun _ h=>suffix_index_zero (code_body_bound _) h⟩
  | leftK => exact ⟨rfl,True.intro⟩
  | leftKV => exact ⟨rfl,binding_leftKV,fun _ h=>suffix_index_zero (code_body_bound _) h⟩
  | rightA => exact ⟨rfl,True.intro⟩
  | rightB => exact ⟨rfl,True.intro⟩
  | rightL => exact ⟨rfl,True.intro⟩
  | rightV => exact ⟨rfl,binding_rightV,fun _ h=>suffix_index_zero (code_body_bound _) h⟩
  | rightJ => exact ⟨rfl,True.intro⟩
  | rightJV => exact ⟨rfl,binding_rightJV,fun _ h=>suffix_index_zero (code_body_bound _) h⟩
  | rightK => exact ⟨rfl,True.intro⟩
  | rightKV => exact ⟨rfl,binding_rightKV,fun _ h=>suffix_index_zero (code_body_bound _) h⟩

private theorem code_coverage (position : Position source.erase) :
    ∃ actual : RootAccess net (),Corresponds net actual.val source.erase position := by
  have existsTerm : ∃u,subtermAt source.erase position.val=some u := by
    cases lookup : subtermAt source.erase position.val with
    | none => have valid:=position.property; rw [lookup] at valid; cases valid
    | some u => exact ⟨u,rfl⟩
  have member := (mem_positions source.erase position.val).mpr existsTerm
  rw [positions_codes] at member
  obtain ⟨c,_inside,equal⟩ := List.mem_map.mp member
  refine ⟨access c,(code_word c).trans equal,termAt c,?_,code_observes c⟩
  simpa only [equal] using lookup_code c

theorem actual_matching : Matches net () source.erase :=
  actual_root_inputs.matches_of_observation_coverage code_coverage

theorem actual_root_access_classification (actual : RootAccess net ()) :
    ∃c : AccessCode,actual.val=edges c ∧ accessWord net actual.val=coordinate c := by
  obtain ⟨u,lookup,_observed⟩ := actual_root_inputs.classify_of_observation_coverage code_coverage actual
  have member := (mem_positions source.erase (accessWord net actual.val)).mpr ⟨u,lookup⟩
  rw [positions_codes] at member
  obtain ⟨c,_inside,equal⟩ := List.mem_map.mp member
  have same : actual=access c := actual_root_inputs.accessWord_injective (equal.symm.trans (code_word c).symm)
  exact ⟨c,congrArg Subtype.val same,equal.symm⟩

theorem actual_binding_suffix_index (actual : RootAccess net ()) {j : Nat}
    (suffix : BindingSuffix net actual.val j) : j=0 := by
  obtain ⟨c,same,_word⟩ := actual_root_access_classification actual
  rw [same] at suffix
  exact suffix_index_zero (code_body_bound c) suffix

#print axioms actual_matching
#print axioms actual_root_access_classification
#print axioms actual_binding_suffix_index

end Lamping.Checks.Q0LocalModelFixture
