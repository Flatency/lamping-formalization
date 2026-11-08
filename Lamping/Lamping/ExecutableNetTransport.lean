import Lamping.Lamping.ExecutableEncoding
import Lamping.Lamping.ReadbackMachine
import Lamping.Lamping.GlobalGraphSteps

namespace Lamping.Graph

/-- Compare inverse images using the supplied algorithm. No equality oracle
or classical choice is introduced by transporting through an explicit bijection. -/
def Bij.transportDecidableEq (bijection : Bij A B) (equal : DecidableEq A) : DecidableEq B :=
  fun left right => match equal (bijection.invFun left) (bijection.invFun right) with
    | .isTrue same => .isTrue (by
        have image := congrArg bijection.toFun same
        simpa only [bijection.right_inv] using image)
    | .isFalse different => .isFalse (fun same => different (congrArg bijection.invFun same))

/-- Restriction to an explicit sum summand retains computational equality. -/
def leftSummandEquality (equal : DecidableEq (A ⊕ B)) : DecidableEq A :=
  fun left right => match equal (.inl left) (.inl right) with
    | .isTrue same => .isTrue (Sum.inl.inj same)
    | .isFalse different => .isFalse (fun same => different (congrArg Sum.inl same))

end Lamping.Graph

namespace Lamping.AG.Readback
open Graph Lambda

/-- Effective graph data contain only the actual graph and carrier equality
algorithms. No readback result, semantic invariant or termination witness is stored. -/
structure ExecutableNet (B : Type) [FiniteNames B] where
  graph : ActualNet B
  nodeEquality : DecidableEq graph.Node
  wireEquality : DecidableEq graph.Wire

namespace ExecutableNet
def ofNet {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
    [DecidableEq N] [DecidableEq W] (g : Net signature N B W) : ExecutableNet B :=
  ⟨ActualNet.ofNet g,inferInstance,inferInstance⟩

def initial (term : Term) : ExecutableNet (Boundary term) :=
  ⟨ActualNet.initial term,(encodedCarrierEquality 0 term).1,(encodedCarrierEquality 0 term).2⟩

def transport {B : Type} [FiniteNames B] (source : ExecutableNet B)
    (target : ActualNet B) (same : NetIso source.graph.net target.net) : ExecutableNet B :=
  ⟨target,same.nodes.transportDecidableEq source.nodeEquality,
    same.vertices.transportDecidableEq source.wireEquality⟩

def runFuel {B : Type} [FiniteNames B] [DecidableEq B]
    (source : ExecutableNet B) (root : B) (fuel : Nat) : MachineRun source.graph.net := by
  letI := source.nodeEquality
  letI := source.wireEquality
  exact readbackFuel source.graph.net root fuel

end ExecutableNet

def Schema.rightNodeEquality (schema : Schema) : DecidableEq schema.right.N := by
  cases schema <;> simp only [Schema.right] <;> infer_instance

def Schema.rightWireEquality (schema : Schema) : DecidableEq schema.right.W := by
  cases schema <;> simp only [Schema.right] <;> infer_instance

section
variable {B : Type} [FiniteNames B]

/-- A rewrite recipe supplies an actual site and a computable source
isomorphism as data. It does not select them from an existential GraphStep. -/
structure ExplicitRewriteRecipe (source : ExecutableNet B) (schema : Schema) where
  Kept : Type
  OutsideWire : Type
  InternalWire : Type
  keptFinite : FiniteNames Kept
  outsideFinite : FiniteNames OutsideWire
  internalFinite : FiniteNames InternalWire
  kept : Kept → Graph.Label signature
  site : PathSite schema kept (B:=B) (W:=OutsideWire) (V:=InternalWire)
  sourceIso : letI := keptFinite
    letI := outsideFinite
    letI := internalFinite
    NetIso source.graph.net site.net

attribute [instance] ExplicitRewriteRecipe.keptFinite ExplicitRewriteRecipe.outsideFinite
  ExplicitRewriteRecipe.internalFinite

namespace ExplicitRewriteRecipe
variable {source : ExecutableNet B} {schema : Schema}

/-- Kept names inherit equality through the actual source carrier map. -/
def keptEquality (recipe : ExplicitRewriteRecipe source schema) : DecidableEq recipe.Kept :=
  leftSummandEquality (recipe.sourceIso.nodes.transportDecidableEq source.nodeEquality)

def outsideWireEquality (recipe : ExplicitRewriteRecipe source schema) : DecidableEq recipe.OutsideWire :=
  leftSummandEquality (recipe.sourceIso.vertices.transportDecidableEq source.wireEquality)

/-- Build the actual RHS and its equality algorithms from the explicit
recipe. The internal-wire carrier disappears; no equality for it is guessed. -/
def target (recipe : ExplicitRewriteRecipe source schema) : ExecutableNet B := by
  letI := recipe.keptEquality
  letI := recipe.outsideWireEquality
  letI := Schema.rightNodeEquality schema
  letI := Schema.rightWireEquality schema
  letI : DecidableEq schema.Frontier := inferInstanceAs (DecidableEq (Aux schema.active ⊕ Aux schema.passive))
  exact ExecutableNet.ofNet recipe.site.reduce

theorem target_graph (recipe : ExplicitRewriteRecipe source schema) :
    recipe.target.graph=ActualNet.ofNet recipe.site.reduce := rfl

theorem actual_step (recipe : ExplicitRewriteRecipe source schema) :
    GraphStep schema source.graph recipe.target.graph :=
  .atSite recipe.kept recipe.site recipe.sourceIso (.refl _)

end ExplicitRewriteRecipe
end
end Lamping.AG.Readback
