import Lamping.Lambda.SyntaxIncidence
import Lamping.Lambda.PrerequisiteEdgeOrder
import Lamping.Lamping.ChainIncidenceIso

namespace Lamping.AG
open Graph Lambda Lambda.Labelled

/-- The actual closed, variable-back-connected syntax incidence structure.
Vertex and edge identities are occurrences, never label values. -/
noncomputable def syntaxIncidenceGraph (current : LTerm) (closed : Closed current.erase) :
    EdgeLabelledIncidence where
  Vertex := SyntaxIncidence.Vertex current
  Edge := SyntaxIncidence.Edge current
  source := SyntaxIncidence.source current
  target := SyntaxIncidence.target current closed
  label := SyntaxIncidence.label current

/-- Edge-induced syntax subgraph. This definition alone makes no chain,
connectedness, isomorphism or physical-representation assertion. -/
noncomputable def chainSyntaxIncidence (current : LTerm) (closed : Closed current.erase)
    (edges : List Path) : EdgeLabelledIncidence :=
  (syntaxIncidenceGraph current closed).induced (fun edge=>edge.val∈edges)

/-- For a genuine chain the edge-membership construction cannot erase
repeated edge occurrences: absence of repeats was independently proved. -/
theorem chainSyntaxIncidence_no_repeated_edges (chain : PrerequisiteChain current p edges) :
    edges.Nodup := chain.nodup

/-- This equality does not identify the distinguished reading starts. They
are deliberately not fields of a bare edge-induced incidence graph. -/
noncomputable def chainSyntaxIncidence_same_edges_iso (current : LTerm) (closed : Closed current.erase)
    (_first : PrerequisiteChain current p edges) (_second : PrerequisiteChain current q edges) :
    ChainIncidenceIso (chainSyntaxIncidence current closed edges)
      (chainSyntaxIncidence current closed edges) :=
  ChainIncidenceIso.refl _

end Lamping.AG