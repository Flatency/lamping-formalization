import Lamping.Lambda.LabelAlternation
namespace Lamping.Lambda.Labelled

/-- Static lambda-graph ports identified by original node labels. Binding
ports are distinct from context/body ports, even for the same lambda. -/
inductive SourcePort where
  | external
  | appContext : Label → SourcePort
  | appFn : Label → SourcePort
  | appArg : Label → SourcePort
  | lamContext : Label → SourcePort
  | lamBody : Label → SourcePort
  | lamBind : Label → SourcePort
  | free : Nat → SourcePort
  deriving DecidableEq, Repr

/-- The environment stores original binder identities, nearest first.
Free variables preserve the index relative to the outer environment. -/
def sourceBinder (env : List Label) (i : Nat) : SourcePort :=
  match env[i]? with
  | some l => .lamBind l
  | none => .free (i-env.length)

@[simp] theorem sourceBinder_zero (env : List Label) (l) : sourceBinder (l::env) 0=.lamBind l := rfl
@[simp] theorem sourceBinder_succ (env : List Label) (l) (i) :
    sourceBinder (l::env) (i+1)=sourceBinder env i := by
  simp only [sourceBinder,List.getElem?_cons_succ,List.length_cons]
  split <;> simp_all [Nat.add_sub_add_right]

structure SourceEdge where
  atom : Label
  fromPort : SourcePort
  toPort : SourcePort
  deriving DecidableEq, Repr

/-- The source edge incident to the current subterm; a variable goes to its
actual de Bruijn binder, rather than creating a fresh syntax node. -/
def sourceEdge (env : List Label) (atPort : SourcePort) : LTerm → SourceEdge
  | .var l i => ⟨l,atPort,sourceBinder env i⟩
  | .lam l _ => ⟨l,atPort,.lamContext l⟩
  | .app l _ _ => ⟨l,atPort,.appContext l⟩

def sourceEdges (env : List Label) (atPort : SourcePort) : LTerm → List SourceEdge
  | .var l i => [⟨l,atPort,sourceBinder env i⟩]
  | .lam l b => ⟨l,atPort,.lamContext l⟩ :: sourceEdges (l::env) (.lamBody l) b
  | .app l f a => ⟨l,atPort,.appContext l⟩ ::
      (sourceEdges env (.appFn l) f ++ sourceEdges env (.appArg l) a)

theorem sourceEdges_atoms (t : LTerm) (env : List Label) (atPort) :
    (sourceEdges env atPort t).map SourceEdge.atom=t.labels := by
  induction t generalizing env atPort with
  | var => rfl
  | lam _ _ ih => simp [sourceEdges,LTerm.labels,ih]
  | app _ _ _ hf ha => simp [sourceEdges,LTerm.labels,hf,ha]

/-- INIT's global label distinctness gives unique original edges. -/
theorem sourceEdges_atom_nodup (hi : INIT t) (env : List Label) (atPort) :
    ((sourceEdges env atPort t).map SourceEdge.atom).Nodup := by
  rw [sourceEdges_atoms]; exact hi.2

private theorem atom_unique (edges : List SourceEdge) (nd : (edges.map SourceEdge.atom).Nodup)
    (he : e∈edges) (hf : f∈edges) (same : e.atom=f.atom) : e=f := by
  induction edges with
  | nil => cases he
  | cons a edges ih =>
    obtain ⟨head,tail⟩ := List.nodup_cons.mp nd
    simp only [List.mem_cons] at he hf
    rcases he with rfl | he
    · rcases hf with rfl | hf
      · rfl
      · exact False.elim (head (List.mem_map.mpr ⟨f,hf,same.symm⟩))
    · rcases hf with rfl | hf
      · exact False.elim (head (List.mem_map.mpr ⟨e,he,same⟩))
      · exact ih tail he hf

theorem sourceEdges_unique (hi : INIT t) (he : e∈sourceEdges env atPort t)
    (hf : f∈sourceEdges env atPort t) (same : e.atom=f.atom) : e=f :=
  atom_unique _ (sourceEdges_atom_nodup hi env atPort) he hf same

theorem sourceEdges_has_label (hl : l∈t.labels) :
    ∃ e∈sourceEdges env atPort t, e.atom=l := by
  rw [← sourceEdges_atoms t env atPort] at hl
  exact List.mem_map.mp hl

/-- The label's atom property is an actual INIT consequence for each edge. -/
theorem sourceEdges_atomic (hi : INIT t) (he : e∈sourceEdges env atPort t) : IsAtomic e.atom := by
  apply hi.1
  rw [← sourceEdges_atoms t env atPort]
  exact List.mem_map.mpr ⟨e,he,rfl⟩

-- Closed-source root and the distinct binding/body ports remain observable.
example (l a : Label) : sourceEdges [] .external (.lam l (.var a 0)) =
    [⟨l,.external,.lamContext l⟩,⟨a,.lamBody l,.lamBind l⟩] := rfl
example (l a : Label) : sourceEdges [] .external (.lam l (.var a 1)) =
    [⟨l,.external,.lamContext l⟩,⟨a,.lamBody l,.free 0⟩] := rfl
end Lamping.Lambda.Labelled
