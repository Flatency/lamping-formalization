import Lamping.Lamping.Fixtures
import Lamping.Lamping.NetIsoInvariantTransport
namespace Lamping.AG
open Graph Lambda

abbrev InitialBetaNodes := AppNodes identity identity ⊕ ((Unit⊕Unit)⊕(Unit⊕Unit))
abbrev InitialBetaVertices := (Empty⊕(IdentityW⊕IdentityW))⊕(Boundary identity⊕Boundary identity)

def betaEncodingNodes : Bij InitialBetaNodes (BetaKept⊕(Unit⊕Unit)) where
  toFun
    | .inl (.inl _) => .inr (.inl ())
    | .inl (.inr (.inl x)) => False.elim (noIdentityFV x)
    | .inl (.inr (.inr x)) => False.elim (noIdentityFV x.val)
    | .inr (.inl (.inl _)) => .inr (.inr ())
    | .inr (.inl (.inr _)) => .inl (.inl ())
    | .inr (.inr (.inl _)) => .inl (.inr (.inl ()))
    | .inr (.inr (.inr _)) => .inl (.inr (.inr ()))
  invFun
    | .inr (.inl _) => .inl (.inl ())
    | .inr (.inr _) => .inr (.inl (.inl ()))
    | .inl (.inl _) => .inr (.inl (.inr ()))
    | .inl (.inr (.inl _)) => .inr (.inr (.inl ()))
    | .inl (.inr (.inr _)) => .inr (.inr (.inr ()))
  left_inv := by
    rintro ((u | (x | x)) | ((v | w) | (y | z)))
    · cases u; rfl
    · exact False.elim (noIdentityFV x)
    · exact False.elim (noIdentityFV x.val)
    · cases v; rfl
    · cases w; rfl
    · cases y; rfl
    · cases z; rfl
  right_inv := by
    rintro ((u | (v | w)) | (x | y)) <;> first | (rename_i t; cases t; rfl) | rfl

def betaEncodingVertices : Bij InitialBetaVertices (BetaW⊕Unit) where
  toFun
    | .inl (.inl e) => nomatch e
    | .inl (.inr w) => .inl (.inl w)
    | .inr (.inl (.inl _)) => .inr ()
    | .inr (.inl (.inr x)) => False.elim (noIdentityFV x)
    | .inr (.inr (.inl _)) => .inl (.inr ())
    | .inr (.inr (.inr x)) => False.elim (noIdentityFV x)
  invFun
    | .inl (.inl w) => .inl (.inr w)
    | .inl (.inr _) => .inr (.inr (.inl ()))
    | .inr _ => .inr (.inl (.inl ()))
  left_inv := by
    rintro ((e | w) | ((u | x) | (u | x)))
    · exact nomatch e
    · rfl
    · cases u; rfl
    · exact False.elim (noIdentityFV x)
    · cases u; rfl
    · exact False.elim (noIdentityFV x)
  right_inv := by rintro ((w|u)|u); rfl; cases u; rfl; cases u; rfl

def betaEncodingPorts : Bij (NodePort signature InitialBetaNodes identityAppNet.label)
    (NodePort signature (BetaKept⊕(Unit⊕Unit)) BetaLabel) where
  toFun
    | ⟨.inl (.inl _),p⟩ => ⟨.inr (.inl ()),p⟩
    | ⟨.inl (.inr (.inl x)),_⟩ => False.elim (noIdentityFV x)
    | ⟨.inl (.inr (.inr x)),_⟩ => False.elim (noIdentityFV x.val)
    | ⟨.inr (.inl (.inl _)),p⟩ => ⟨.inr (.inr ()),p⟩
    | ⟨.inr (.inl (.inr _)),p⟩ => ⟨.inl (.inl ()),p⟩
    | ⟨.inr (.inr (.inl _)),p⟩ => ⟨.inl (.inr (.inl ())),p⟩
    | ⟨.inr (.inr (.inr _)),p⟩ => ⟨.inl (.inr (.inr ())),p⟩
  invFun
    | ⟨.inr (.inl _),p⟩ => ⟨.inl (.inl ()),p⟩
    | ⟨.inr (.inr _),p⟩ => ⟨.inr (.inl (.inl ())),p⟩
    | ⟨.inl (.inl _),p⟩ => ⟨.inr (.inl (.inr ())),p⟩
    | ⟨.inl (.inr (.inl _)),p⟩ => ⟨.inr (.inr (.inl ())),p⟩
    | ⟨.inl (.inr (.inr _)),p⟩ => ⟨.inr (.inr (.inr ())),p⟩
  left_inv := by
    rintro ⟨((u | (x | x)) | ((v | w) | (y | z))),p⟩
    · cases u; rfl
    · exact False.elim (noIdentityFV x)
    · exact False.elim (noIdentityFV x.val)
    · cases v; rfl
    · cases w; rfl
    · cases y; rfl
    · cases z; rfl
  right_inv := by
    rintro ⟨((u | (v | w)) | (x | y)),p⟩
    · cases u; rfl
    · cases v; rfl
    · cases w; rfl
    · cases x; rfl
    · cases y; rfl

/-- The actual encoder fixture is a boundary-fixed, port-role-preserving net
isomorphism, not just an arbitrary bijection of endpoint carriers. -/
def betaEncodingIso : NetIso identityAppNet actualBetaSite.net where
  nodes := betaEncodingNodes
  vertices := betaEncodingVertices
  labels := by
    rintro ((u | (x | x)) | ((v | w) | (y | z)))
    · rfl
    · exact False.elim (noIdentityFV x)
    · exact False.elim (noIdentityFV x.val)
    · rfl
    · rfl
    · rfl
    · rfl
  ports := betaEncodingPorts
  port_node := by
    rintro ⟨((u | (x | x)) | ((v | w) | (y | z))),p⟩
    · rfl
    · exact False.elim (noIdentityFV x)
    · exact False.elim (noIdentityFV x.val)
    · rfl
    · rfl
    · rfl
    · rfl
  port_role := by
    rintro ⟨((u | (x | x)) | ((v | w) | (y | z))),p⟩
    · rfl
    · exact False.elim (noIdentityFV x)
    · exact False.elim (noIdentityFV x.val)
    · rfl
    · rfl
    · rfl
    · rfl
  ends := betaEncodingEnds
  node_end := by
    rintro ⟨((u | (x | x)) | ((v | w) | (y | z))),p⟩
    · rfl
    · exact False.elim (noIdentityFV x)
    · exact False.elim (noIdentityFV x.val)
    · rfl
    · rfl
    · rfl
    · rfl
  boundary_end _ := rfl
  vertex_end := by
    rintro ((e | (w | w)) | ((u | x) | (u | x))) d
    · exact nomatch e
    · rfl
    · rfl
    · rfl
    · exact False.elim (noIdentityFV x)
    · rfl
    · exact False.elim (noIdentityFV x)
  wiring e := (Pairing.rename_apply identityAppNet.wire betaEncodingEnds e).symm
end Lamping.AG
