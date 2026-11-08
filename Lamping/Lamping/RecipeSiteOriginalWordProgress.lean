import Lamping.Lamping.InternalOccursControlProgress
import Lamping.Lamping.RecipeSiteActionProgress
import Lamping.Lamping.WholeCancellationWordProgress

namespace Lamping.Graph
open AG AG.ExposureScheduling
section
variable {N M B W V : Type} [FiniteNames N] [FiniteNames M] [FiniteNames B]
variable [FiniteNames W] [FiniteNames V]
variable {g : Net signature N B W} {h : Net signature M B V}

private def departureControlToken (net : Net signature N B W) (e : Endpoint net) : List Bool :=
  match e with
  | .inl ⟨node,port⟩ => controlPortWord (net.label node).sort port
  | .inr _ => []

private theorem controlToken_cast {x y : Label signature} (eq : x=y) (p : Port x.sort) :
    controlPortWord y.sort (eq ▸ p)=controlPortWord x.sort p := by
  cases eq
  rfl

private theorem departureControlToken_map (iso : NetIso g h) (e : Endpoint g) :
    departureControlToken h (iso.ends e)=departureControlToken g e := by
  rcases e with ⟨n,p⟩ | (b | ⟨w,d⟩)
  · rw [iso.node_end_image]
    exact controlToken_cast (iso.labels n).symm p
  · rw [iso.boundary_end]; rfl
  · rw [iso.vertex_end]; rfl

/-- Exact preservation of the ordered control word under a physical renaming. -/
theorem NetIso.controlWord (iso : NetIso g h) (es : List (Endpoint g)) :
    ExposureScheduling.controlWord h (es.map iso.ends)=ExposureScheduling.controlWord g es := by
  cases es with
  | nil => rfl
  | cons e rest =>
    change (rest.map iso.ends).flatMap (departureControlToken h)=
      rest.flatMap (departureControlToken g)
    rw [List.flatMap_map]
    exact congrArg (fun f => rest.flatMap f) (funext (departureControlToken_map iso))
end
end Lamping.Graph

namespace Lamping.AG.Readback
open Graph Lambda Lambda.Labelled ExposureScheduling
section
variable {B : Type} [FiniteNames B] {s : Schema} {source : ExecutableNet B}
variable {root : B} {current : LTerm} {redex : RedexOcc current.erase}

theorem ExplicitRewriteRecipe.mappedRedexAccess_controlWord
    (recipe : ExplicitRewriteRecipe source s)
    (access : ActualRedexAccess source.graph.net root redex) :
    controlWord recipe.site.net (recipe.sourceIso.actualRedexAccess access).connection.edges=
      controlWord source.graph.net access.connection.edges := by
  rw [recipe.mappedRedexAccess_edges access]
  exact recipe.sourceIso.controlWord access.connection.edges

/-- Compare the actual internal-action target with the original graph word. -/
theorem ExplicitRewriteRecipe.internalActionProgress_original
    (recipe : ExplicitRewriteRecipe source s)
    (action : IsAction s)
    (activeControl : s.active=.fan ∨ s.active=.cro ∨ s.active=.bra)
    (passiveControl : s.passive=.fan ∨ s.passive=.cro ∨ s.passive=.bra)
    (access : ActualRedexAccess source.graph.net root redex)
    (matching : Matches source.graph.net root current.erase) (inputs : RootInputs source.graph.net root)
    {directions : B → Bool} {depths : B → Int}
    (flow : Nonempty (FlowBalance source.graph.net directions)) (positive : directions root=true)
    (balance : Nonempty (IndexedLevelBalance source.graph.net depths)) (rootDepth : depths root=0)
    (oldT : Transparency source.graph.net root)
    (principal : SiteActionPrincipal recipe.site)
    (internal : Bool ⊕ (recipe.InternalWire × Bool))
    (selected : recipe.site.internalEnd internal ∈ access.connection.edges.map recipe.sourceIso.ends) :
    ∃ target : ActualRedexAccess recipe.target.graph.net root redex,
      (controlWord recipe.target.graph.net target.connection.edges).length =
        (controlWord source.graph.net access.connection.edges).length ∧
      inversions (controlWord recipe.target.graph.net target.connection.edges) <
        inversions (controlWord source.graph.net access.connection.edges) := by
  obtain ⟨target,length,strict⟩ := recipe.internalActionProgress action activeControl passiveControl
    access matching inputs flow positive balance rootDepth oldT principal internal selected
  rw [recipe.mappedRedexAccess_controlWord access] at length strict
  exact ⟨target,length,strict⟩

/-- The actual cancellation target deletes letters from the original control word. -/
theorem ExplicitRewriteRecipe.cancellationProgress_original
    (recipe : ExplicitRewriteRecipe source s) (cancel : IsCancellation s)
    (closed : Closed current.erase)
    (access : ActualRedexAccess source.graph.net root redex)
    (matching : Matches source.graph.net root current.erase) (inputs : RootInputs source.graph.net root)
    {directions : B → Bool} {depths : B → Int}
    (flow : Nonempty (FlowBalance source.graph.net directions)) (positive : directions root=true)
    (balance : Nonempty (IndexedLevelBalance source.graph.net depths)) (rootDepth : depths root=0)
    (oldT : Transparency source.graph.net root)
    (appStamp lamStamp : Lambda.Labelled.Label) (body arg : LTerm)
    (lookup : current.subterm redex.val=some (.app appStamp (.lam lamStamp body) arg))
    (internal : Bool ⊕ (recipe.InternalWire × Bool))
    (selected : recipe.site.internalEnd internal ∈ access.connection.edges.map recipe.sourceIso.ends) :
    ∃ target : ActualRedexAccess recipe.target.graph.net root redex,
      (controlWord recipe.target.graph.net target.connection.edges).length <
        (controlWord source.graph.net access.connection.edges).length := by
  let iso := recipe.sourceIso
  let mapped := iso.actualRedexAccess access
  obtain ⟨flow⟩ := flow
  obtain ⟨balance⟩ := balance
  obtain ⟨_a,_b,labels⟩ := access.connection.proper.1
  obtain ⟨target,_labels,_n,_positive,_erasure,strict⟩ :=
    ActualRedexAccess.cancellation_control_count_progress_of_internal_occurs recipe.site cancel
      (iso.flowBalance flow) positive (iso.rootInputs inputs) (iso.indexed_balance balance)
      rootDepth (iso.transparency oldT) closed (iso.matches matching) redex
      appStamp lamStamp body arg lookup mapped (iso.labelling labels) internal selected
  change (controlWord recipe.target.graph.net target.connection.edges).length <
    (controlWord recipe.site.net (recipe.sourceIso.actualRedexAccess access).connection.edges).length at strict
  rw [recipe.mappedRedexAccess_controlWord access] at strict
  exact ⟨target,strict⟩
end
end Lamping.AG.Readback
