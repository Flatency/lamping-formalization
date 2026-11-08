import Lamping.Lambda.PrerequisiteEdgeOrder
namespace Lamping.Lambda.Labelled
/-- A dependency chain starting at a lambda cannot reenter its body.
This follows the actual occurrence order, not a label or graph hypothesis. -/
theorem PrerequisiteChain.excludes_lambda_body (chain : PrerequisiteChain t parent edges)
    (atLambda : t.subterm parent=some (.lam stamp body)) :
    parent++(.body::descendant)∉edges := by
  intro member
  have bound := chain.edge_order_le member
  obtain ⟨offset,order⟩ := prerequisiteOrder_subtree atLambda
  have root := order []
  have child := order (.body::descendant)
  simp only [List.append_nil,prerequisiteOrder] at root child
  omega
end Lamping.Lambda.Labelled
