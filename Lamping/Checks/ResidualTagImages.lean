import Lamping.Lambda.ResidualTagImages

namespace Lamping.Checks.ResidualTagImagesChecks
open Lambda Lambda.Labelled

abbrev I : Term := .lam (.var 0)
abbrev rootContract : LTerm → LTerm
  | .app beta (.lam alpha body) arg => LTerm.contract beta alpha body arg
  | t => t
abbrev markedContract : Marked → Marked
  | .red _ body arg => Marked.contract body arg
  | .app _ (.lam body) arg => Marked.contract body arg
  | t => t

namespace Retained
abbrev bare : Term := .app (.lam (.app I I)) I
abbrev source : LTerm := initLabels bare
abbrev body : LTerm := .app (.atom 2) (.lam (.atom 3) (.var (.atom 4) 0))
  (.lam (.atom 5) (.var (.atom 6) 0))
abbrev arg : LTerm := .lam (.atom 7) (.var (.atom 8) 0)
abbrev target : LTerm := rootContract source
abbrev F : List Path := [[],[.fn,.body]]
abbrev marked : Marked := Marked.mark F source.erase
abbrev result : Marked := markedContract marked

theorem initial : INIT source := init_is_INIT _
theorem closed : Closed source.erase := by
  change ((0<2) ∧(0<2)) ∧(0<1)
  decide
def step : Labelled.StepAt [] source target := .root _ _ _ _
def reduction : Marked.ReductionAt [] marked result := .redRoot _ _ _
def origin : BetaNodePreimage body arg [] [] [.fn,.body] :=
  .retained (relative:=[]) (show body.subterm []=some body from rfl)
    (by intro stamp impossible;cases impossible)

theorem tag_image : []∈Marked.tracePositions [.fn,.body] result := by
  obtain ⟨stamp,fn,arg,lookup⟩ : ∃stamp fn arg,
      target.subterm []=some (.app stamp fn arg) := ⟨_,_,_,rfl⟩
  exact reduction.trace_node_image (Marked.valid_mark F source.erase) step
    (Marked.erase_mark F source.erase).symm rfl origin lookup (by decide)

/-- SOURCE selected root tag has no surviving operational APP origin. -/
theorem selected_root_deleted (p : Path) : ¬BetaNodePreimage body arg [] p [] := by
  intro occurrence
  rcases occurrence.coordinates with ⟨same,outside⟩ |
      ⟨relative,node,current,old,lookup,nonselected⟩ |
      ⟨whereCopy,relative,node,occurs,current,old,lookup⟩
  · exact outside ⟨p,rfl⟩
  · have length := congrArg List.length old
    simp only [List.length_cons,List.length_nil,List.length_append] at length
    omega
  · have length := congrArg List.length old
    simp only [List.length_cons,List.length_nil,List.length_append] at length
    omega

theorem root_tag_really_consumed : Marked.tracePositions [] result=[] := by decide
end Retained

namespace Copied
abbrev bare : Term := .app (.lam (.app (.var 0) (.var 0))) (.app I I)
abbrev source : LTerm := initLabels bare
abbrev body : LTerm := .app (.atom 2) (.var (.atom 3) 0) (.var (.atom 4) 0)
abbrev arg : LTerm := .app (.atom 5) (.lam (.atom 6) (.var (.atom 7) 0))
  (.lam (.atom 8) (.var (.atom 9) 0))
abbrev target : LTerm := rootContract source
abbrev F : List Path := [[],[.arg]]
abbrev marked : Marked := Marked.mark F source.erase
abbrev result : Marked := markedContract marked

theorem initial : INIT source := init_is_INIT _
theorem closed : Closed source.erase := by
  change ((0<1) ∧(0<1)) ∧((0<1) ∧(0<1))
  decide
def step : Labelled.StepAt [] source target := .root _ _ _ _
def reduction : Marked.ReductionAt [] marked result := .redRoot _ _ _
def leftOrigin : BetaNodePreimage body arg [] [.fn] [.arg] :=
  .copied (site:=[]) (q:=[.fn]) (relative:=[]) (show ArgumentOccurrence body.erase [.fn] from rfl)
    (show arg.subterm []=some arg from rfl)
def rightOrigin : BetaNodePreimage body arg [] [.arg] [.arg] :=
  .copied (site:=[]) (q:=[.arg]) (relative:=[]) (show ArgumentOccurrence body.erase [.arg] from rfl)
    (show arg.subterm []=some arg from rfl)

theorem left_tag_image : [.fn]∈Marked.tracePositions [.arg] result := by
  obtain ⟨stamp,fn,arg,lookup⟩ : ∃stamp fn arg,
      target.subterm [.fn]=some (.app stamp fn arg) := ⟨_,_,_,rfl⟩
  exact reduction.trace_node_image (Marked.valid_mark F source.erase) step
    (Marked.erase_mark F source.erase).symm rfl leftOrigin lookup (by decide)

theorem right_tag_image : [.arg]∈Marked.tracePositions [.arg] result := by
  obtain ⟨stamp,fn,arg,lookup⟩ : ∃stamp fn arg,
      target.subterm [.arg]=some (.app stamp fn arg) := ⟨_,_,_,rfl⟩
  exact reduction.trace_node_image (Marked.valid_mark F source.erase) step
    (Marked.erase_mark F source.erase).symm rfl rightOrigin lookup (by decide)

theorem different_copies : ([.fn]:Path)≠[.arg] := by decide
end Copied

namespace Context
abbrev source : LTerm := Retained.source
abbrev localTarget : LTerm := LTerm.contract (.atom 2) (.atom 3)
  (.var (.atom 4) 0) (.lam (.atom 5) (.var (.atom 6) 0))
abbrev target : LTerm := .app (.atom 0) (.lam (.atom 1) localTarget) Retained.arg
abbrev marked : Marked := Retained.marked
abbrev result : Marked := .red [[]] (Marked.contract (.var 0) (.lam (.var 0))) (.lam (.var 0))

def step : Labelled.StepAt [.fn,.body] source target := .fn (.body (.root _ _ _ _))
def reduction : Marked.ReductionAt [.fn,.body] marked result := .redL (.redRoot _ _ _)
def origin : BetaNodePreimage (.var (.atom 4) 0) (.lam (.atom 5) (.var (.atom 6) 0))
    [.fn,.body] [] [] := .context (by rintro ⟨rest,impossible⟩;cases impossible)

/-- A tag at the strict APP ancestor of the redex remains at that literal APP. -/
theorem ancestor_tag_image : []∈Marked.tracePositions [] result := by
  exact reduction.trace_node_image (Marked.valid_mark Retained.F source.erase) step
    (Marked.erase_mark Retained.F source.erase).symm rfl origin
    (show target.subterm []=some (.app (.atom 0) (.lam (.atom 1) localTarget) Retained.arg) from rfl)
    (by decide)
end Context

#print axioms Retained.initial
#print axioms Retained.closed
#print axioms Retained.tag_image
#print axioms Retained.selected_root_deleted
#print axioms Retained.root_tag_really_consumed
#print axioms Copied.initial
#print axioms Copied.closed
#print axioms Copied.left_tag_image
#print axioms Copied.right_tag_image
#print axioms Copied.different_copies
#print axioms Context.ancestor_tag_image
end Lamping.Checks.ResidualTagImagesChecks
