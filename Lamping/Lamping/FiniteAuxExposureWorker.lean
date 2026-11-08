import Lamping.Lamping.ComputedAuxExposureTransition
import Lamping.Lamping.ExecutableRewritePrograms

namespace Lamping.AG.ExposureScheduling
open Graph Lambda Lambda.Labelled Readback

/-- The fixed labelled occurrence supplies only the proof of progress. -/
def LabelledExposureOccurrence (term : Term) (redex : RedexOcc term) : Prop :=
  ∃ current : LTerm, current.erase=term ∧ Closed term ∧
    ∃ (appStamp lamStamp : Lambda.Labelled.Label) (body arg : LTerm),
      current.subterm redex.val=some (.app appStamp (.lam lamStamp body) arg)

private theorem wordDecreaseLex {new old : List Bool}
    (strict : ControlWordDecrease new old) :
    Prod.Lex (fun a b : Nat => a<b) (fun a b : Nat => a<b)
      (new.length,inversions new) (old.length,inversions old) := by
  rcases strict with shorter | ⟨same,fewer⟩
  · apply Prod.Lex.left
    exact shorter
  · rw [same]
    apply Prod.Lex.right
    exact fewer

section
variable {B : Type} [FiniteNames B] [DecidableEq B]
variable {root : B} {term : Term} {directions : B → Bool}

private theorem strictOfLabelledOccurrence (source : ExecutableNet B)
    (domain : AuxExposureDomain source.graph root term directions) (redex : RedexOcc term)
    (labelled : LabelledExposureOccurrence term redex)
    (nonempty : controlWord source.graph.net (auxExposureAccess source domain redex).connection.edges≠[]) :
    let step := auxExposureTransition source domain redex nonempty
    ControlWordDecrease (controlWord step.recipe.target.graph.net step.targetAccess.connection.edges)
      (controlWord source.graph.net (auxExposureAccess source domain redex).connection.edges) := by
  obtain ⟨current,erase,closed,appStamp,lamStamp,body,arg,lookup⟩ := labelled
  subst term
  exact auxExposureTransition_strict source domain redex closed appStamp lamStamp body arg lookup nonempty

/-- A finite auxiliary run ending at the computed zero-control access of the
same redex path. Its final executable graph is retained. -/
structure FiniteAuxExposure (source : ExecutableNet B) (root : B)
    (term : Term) (redex : RedexOcc term) (directions : B → Bool) where
  target : ExecutableNet B
  domain : AuxExposureDomain target.graph root term directions
  schemas : List Schema
  trace : GraphTrace source.graph target.graph schemas
  auxOnly : ∀ schema∈schemas, ∀ i, schema≠.beta i
  emptyWord : controlWord target.graph.net (auxExposureAccess target domain redex).connection.edges=[]
  program : ExecutableProgram source
  programResult : program.result=target
  programSchemas : program.schemas=schemas

def FiniteAuxExposure.access {source : ExecutableNet B} {redex : RedexOcc term}
    (result : FiniteAuxExposure source root term redex directions) :
    ActualRedexAccess result.target.graph.net root redex :=
  auxExposureAccess result.target result.domain redex

/-- Run the actual auxiliary selector until the fixed occurrence has no
control letters. The recursion measure refers only to computed accesses. -/
def finiteAuxExposure (redex : RedexOcc term) (labelled : LabelledExposureOccurrence term redex)
    (source : ExecutableNet B) (domain : AuxExposureDomain source.graph root term directions) :
    FiniteAuxExposure source root term redex directions :=
  if empty : controlWord source.graph.net (auxExposureAccess source domain redex).connection.edges=[] then
    ⟨source,domain,[],GraphTrace.refl source.graph,by simp,empty,.stop source,rfl,rfl⟩
  else
    let step := auxExposureTransition source domain redex empty
    let rest := finiteAuxExposure redex labelled step.recipe.target step.domain
    ⟨rest.target,rest.domain,step.schema::rest.schemas,
      GraphTrace.cons step.recipe.actual_step rest.trace,
      by
        intro schema member i
        rcases List.mem_cons.mp member with same | later
        · exact same.symm ▸ step.notBeta i
        · exact rest.auxOnly schema later i,
      rest.emptyWord,.rewrite step.recipe rest.program,rest.programResult,
      congrArg (List.cons step.schema) rest.programSchemas⟩
termination_by
  let word := controlWord source.graph.net (auxExposureAccess source domain redex).connection.edges
  (word.length,inversions word)
decreasing_by
  exact wordDecreaseLex (strictOfLabelledOccurrence source domain redex labelled empty)
end
end Lamping.AG.ExposureScheduling
