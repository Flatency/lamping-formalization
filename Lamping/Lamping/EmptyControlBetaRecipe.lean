import Lamping.Lamping.ExposureControlWords
import Lamping.Lamping.FirstNodeDecomposition
import Lamping.Lamping.BalancedPrincipalRoutes
import Lamping.Lamping.MatchingRedexEndpointUniqueness
import Lamping.Lamping.ExecutableCorridorPresentation

namespace Lamping.AG
open Graph Lambda ExposureScheduling

private theorem zip_right_member {A C : Type} {xs : List A} {ys : List C} {a : A} {b : C}
    (member : (a,b)∈xs.zip ys) : b∈ys := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons x xs ih =>
    cases ys with
    | nil => simp at member
    | cons y ys =>
      rcases List.mem_cons.mp member with same |rest
      · exact List.mem_cons.mpr (Or.inl (congrArg Prod.snd same))
      · exact List.mem_cons_of_mem _ (ih rest)

private theorem control_letter_nonempty (kind : Kind) (port : Port kind)
    (control : ∃ op,kind=Kind.op op ∧(op=Op.fan ∨op=Op.cro ∨op=Op.bra)) :
    controlPortWord kind port≠[] := by
  rcases control with ⟨op,rfl,controlled⟩
  rcases controlled with rfl|rfl|rfl <;> cases port <;> intro impossible <;> cases impossible

section Connection
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

/-- Empty control word on THIS actual connection excludes every internal
control turn. Transparent turns are a conclusion, never an input oracle. -/
theorem RedexConnection.transparent_of_controlWord_nil (connection : RedexConnection g)
    (empty : controlWord g connection.edges=[]) : TransparentTurns (g:=g) connection.edges := by
  intro e f pair
  have atDeparture := (List.flatMap_eq_nil_iff.mp empty) f (zip_right_member pair)
  rcases connection.control_only e f pair with transparent|
      ⟨node,p,q,op,sort,controlled,_arrives,leaves⟩
  · exact transparent
  · rw [leaves] at atDeparture
    change controlPortWord (g.label node).sort q=[] at atDeparture
    exact False.elim ((control_letter_nonempty (g.label node).sort q ⟨op,sort,controlled⟩) atDeparture)

private def empty_control_corridor (connection : RedexConnection g)
    (empty : controlWord g connection.edges=[]) : TransparentCorridor g where
  first := ⟨connection.app,connection.appPort⟩
  last := ⟨connection.lam,connection.lamPort⟩
  edges := connection.edges
  start := connection.start
  finish := connection.finish
  transparent := connection.transparent_of_controlWord_nil empty

private theorem empty_principal_indices (connection : RedexConnection g)
    {depths : B → Int} (balance : LevelBalance g depths)
    (empty : controlWord g connection.edges=[]) : connection.appIndex=connection.lamIndex :=
  balance.proper_principal_route_indices connection.edges connection.app connection.lam
    connection.appPort connection.lamPort Op.app Op.lam connection.appIndex connection.lamIndex
    connection.appLabel connection.lamLabel (Or.inl rfl) (Or.inr rfl)
    connection.appPrincipal connection.lamPrincipal connection.start connection.finish
    (connection.transparent_of_controlWord_nil empty)

private theorem actual_app_ne_lam (connection : RedexConnection g) : connection.app≠connection.lam := by
  intro same
  have labels := connection.appLabel.symm.trans ((congrArg g.label same).trans connection.lamLabel)
  have kinds := congrArg (fun actual : Graph.Label signature => actual.sort) labels
  cases kinds
end Connection

namespace Readback
section
variable {B : Type} [FiniteNames B] (source : ExecutableNet B)
variable {root : B} {term : Term} {redex : RedexOcc term}

/-- Computable carrier/port data are assembled from the actual finite phi;
all geometric/typing/index arguments below are erased proof fields. -/
private def empty_beta_presentation
    (access : ActualRedexAccess source.graph.net root redex)
    (equal : access.connection.appIndex = access.connection.lamIndex)
    (empty : controlWord source.graph.net access.connection.edges=[]) :
    PhysicalCorridorPresentation source.graph.net (Schema.beta access.connection.appIndex)
      access.connection.app access.connection.lam access.connection.appPort access.connection.lamPort := by
  letI := source.nodeEquality
  letI := source.wireEquality
  let connection := access.connection
  let route : TransparentCorridor source.graph.net := empty_control_corridor connection empty
  exact PhysicalCorridorPresentation.executableOfCorridor source.graph.net
    (Schema.beta connection.appIndex) route connection.app connection.lam (actual_app_ne_lam connection)
    connection.appLabel (by rw [equal];exact connection.lamLabel)
    connection.appPort connection.lamPort connection.appPrincipal connection.lamPrincipal rfl rfl

/-- Only the index-equality proposition enters this actual data builder. -/
def empty_beta_recipe_with_index_eq
    (access : ActualRedexAccess source.graph.net root redex)
    (equal : access.connection.appIndex = access.connection.lamIndex)
    (empty : controlWord source.graph.net access.connection.edges=[]) :
    ExplicitRewriteRecipe source (Schema.beta access.connection.appIndex) :=
  explicitRecipeOfPresentation (empty_beta_presentation source access equal empty)

/-- Eliminate the reachability witness only into the index-equality proposition. -/
theorem empty_beta_recipe_index_eq
    (access : ActualRedexAccess source.graph.net root redex)
    {depths : B → Int} (balance : Nonempty (LevelBalance source.graph.net depths))
    (empty : controlWord source.graph.net access.connection.edges=[]) :
    access.connection.appIndex = access.connection.lamIndex := by
  obtain ⟨witness⟩ := balance
  exact empty_principal_indices access.connection witness empty

/-- Exact source port identities for the proof-only constructor. -/
theorem empty_beta_recipe_with_index_eq_ports
    (access : ActualRedexAccess source.graph.net root redex)
    (equal : access.connection.appIndex = access.connection.lamIndex)
    (empty : controlWord source.graph.net access.connection.edges=[]) :
    (empty_beta_recipe_with_index_eq source access equal empty).sourceIso.ports
      ⟨access.connection.app,access.connection.appPort⟩=⟨Sum.inr (Sum.inl ()),Sum.inl ()⟩ ∧
    (empty_beta_recipe_with_index_eq source access equal empty).sourceIso.ports
      ⟨access.connection.lam,access.connection.lamPort⟩=⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩ :=
  explicitRecipeOfPresentation_ports (empty_beta_presentation source access equal empty)

/-- An explicit beta recipe for the given actual zero-control connection.
No GraphStep/Nonempty witness is selected to obtain program data. -/
def empty_beta_recipe
    (access : ActualRedexAccess source.graph.net root redex)
    {depths : B → Int} (balance : LevelBalance source.graph.net depths)
    (empty : controlWord source.graph.net access.connection.edges=[]) :
    ExplicitRewriteRecipe source (Schema.beta access.connection.appIndex) :=
  empty_beta_recipe_with_index_eq source access (empty_principal_indices access.connection balance empty) empty

/-- The constructed source renaming retains BOTH original physical beta
principal ports, not just an isomorphic or semantically equivalent redex. -/
theorem empty_beta_recipe_ports
    (access : ActualRedexAccess source.graph.net root redex)
    {depths : B → Int} (balance : LevelBalance source.graph.net depths)
    (empty : controlWord source.graph.net access.connection.edges=[]) :
    (empty_beta_recipe source access balance empty).sourceIso.ports
      ⟨access.connection.app,access.connection.appPort⟩=⟨Sum.inr (Sum.inl ()),Sum.inl ()⟩ ∧
    (empty_beta_recipe source access balance empty).sourceIso.ports
      ⟨access.connection.lam,access.connection.lamPort⟩=⟨Sum.inr (Sum.inr ()),Sum.inl ()⟩ :=
  empty_beta_recipe_with_index_eq_ports source access (empty_principal_indices access.connection balance empty) empty

/-- The old API is the same recipe by proof irrelevance, including its target. -/
theorem empty_beta_recipe_eq_with_index_eq
    (access : ActualRedexAccess source.graph.net root redex)
    {depths : B → Int} (balance : LevelBalance source.graph.net depths)
    (equal : access.connection.appIndex = access.connection.lamIndex)
    (empty : controlWord source.graph.net access.connection.edges=[]) :
    empty_beta_recipe source access balance empty =
      empty_beta_recipe_with_index_eq source access equal empty := rfl
end
end Readback
end Lamping.AG
