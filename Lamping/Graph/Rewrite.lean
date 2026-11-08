import Lamping.Graph.Core
namespace Lamping.Graph
variable {S : Signature} {N B W J : Type}
variable [FiniteNames N] [FiniteNames B] [FiniteNames W] [FiniteNames J]
/-- Demote each selected pair of boundary ends into a fresh transparent vertex. -/
def glueEnd (label : N → Label S) :
    Bij (End S N (B ⊕ (J × Bool)) W label) (End S N B (W ⊕ J) label) where
  toFun
    | .inl p => .inl p
    | .inr (.inl (.inl b)) => .inr (.inl b)
    | .inr (.inl (.inr (j,d))) => .inr (.inr (.inr j,d))
    | .inr (.inr (w,d)) => .inr (.inr (.inl w,d))
  invFun
    | .inl p => .inl p
    | .inr (.inl b) => .inr (.inl (.inl b))
    | .inr (.inr (.inl w,d)) => .inr (.inr (w,d))
    | .inr (.inr (.inr j,d)) => .inr (.inl (.inr (j,d)))
  left_inv := by rintro (p | ((b | ⟨j,d⟩) | ⟨w,d⟩)) <;> rfl
  right_inv := by rintro (p | (b | ⟨w | j,d⟩)) <;> rfl

def glue (g : Net S N (B ⊕ (J × Bool)) W) : Net S N B (W ⊕ J) :=
  ⟨g.label, g.wire.rename (glueEnd g.label)⟩
 theorem glue_pairing (g : Net S N (B ⊕ (J × Bool)) W) (e) :
    (glue g).wire ((glue g).wire e) = e := (glue g).wire.involutive e
 theorem glue_boundary (g : Net S N (B ⊕ (J × Bool)) W) (b : B) :
    (glue g).wire (.inr (.inl b)) =
      glueEnd g.label (g.wire (.inr (.inl (.inl b)))) := rfl
/-- Renaming commutes with the actual glue transport, with the induced renaming. -/
theorem rename_glue (g : Net S N (B ⊕ (J × Bool)) W)
    (e : Bij E (End S N (B ⊕ (J × Bool)) W g.label)) (p : Pairing E)
    (h : p.rename e = g.wire) :
    (glue g).wire = p.rename (e.trans (glueEnd g.label)) := by
  change g.wire.rename (glueEnd g.label) = _
  rw [← h]; rfl

/-- Removing an internally closed set of ends actually restricts the matching.
The closure condition describes the chosen cut; it is not target well-formedness. -/
def leftValue (x : E ⊕ I) (h : ∀ i, x ≠ .inr i) : E :=
  match x with
  | .inl e => e
  | .inr i => False.elim (h i rfl)
theorem leftValue_spec (x : E ⊕ I) (h) : x = .inl (leftValue x h) := by
  cases x with
  | inl e => rfl
  | inr i => exact False.elim (h i rfl)
def restrict (p : Pairing (E ⊕ I)) (closed : ∀ e i, p (.inl e) ≠ .inr i) : Pairing E where
  mate e := leftValue (p (.inl e)) (closed e)
  involutive e := by
    apply Sum.inl.inj
    have h := leftValue_spec (p (.inl e)) (closed e)
    have hh := leftValue_spec (p (.inl (leftValue (p (.inl e)) (closed e))))
      (closed (leftValue (p (.inl e)) (closed e)))
    calc
      _ = p (.inl (leftValue (p (.inl e)) (closed e))) := hh.symm
      _ = p (p (.inl e)) := congrArg p h.symm
      _ = .inl e := p.involutive _
  fixedPointFree e := by
    intro he
    have h := leftValue_spec (p (.inl e)) (closed e)
    rw [he] at h
    exact p.fixedPointFree _ h
 theorem restrict_mate (p : Pairing (E ⊕ I)) (h) (x : E) :
    p (.inl x) = .inl ((restrict p h) x) := leftValue_spec _ _
variable {K D F I : Type} [FiniteNames K] [FiniteNames D] [FiniteNames F]
/-- Partition the deleted nodes' named ports into external frontier and genuinely
removed internal ends. No assumptions about distinct surrounding wires. -/
def Bij.sum (a : Bij A B) (b : Bij C D) : Bij (A ⊕ C) (B ⊕ D) where
  toFun := Sum.elim (Sum.inl ∘ a) (Sum.inr ∘ b)
  invFun := Sum.elim (Sum.inl ∘ a.invFun) (Sum.inr ∘ b.invFun)
  left_inv := by rintro (x | x) <;> simp [a.left_inv,b.left_inv]
  right_inv := by rintro (x | x) <;> simp [a.right_inv,b.right_inv]
def cutSplit (label : K ⊕ D → Label S) :
    Bij (End S (K ⊕ D) B W label)
      (End S K B W (fun k => label (.inl k)) ⊕ NodePort S D (fun d => label (.inr d))) where
  toFun
    | .inl ⟨.inl k,p⟩ => .inl (.inl ⟨k,p⟩)
    | .inl ⟨.inr d,p⟩ => .inr ⟨d,p⟩
    | .inr (.inl b) => .inl (.inr (.inl b))
    | .inr (.inr w) => .inl (.inr (.inr w))
  invFun
    | .inl (.inl ⟨k,p⟩) => .inl ⟨.inl k,p⟩
    | .inr ⟨d,p⟩ => .inl ⟨.inr d,p⟩
    | .inl (.inr (.inl b)) => .inr (.inl b)
    | .inl (.inr (.inr w)) => .inr (.inr w)
  left_inv := by rintro (⟨k | d,p⟩ | (b | w)) <;> rfl
  right_inv := by rintro ((⟨k,p⟩ | (b | w)) | ⟨d,p⟩) <;> rfl

def cutJoin (label : K → Label S) :
    Bij (End S K B W label ⊕ (F ⊕ I)) (End S K (B ⊕ F) W label ⊕ I) where
  toFun
    | .inl (.inl p) => .inl (.inl p)
    | .inl (.inr (.inl b)) => .inl (.inr (.inl (.inl b)))
    | .inl (.inr (.inr w)) => .inl (.inr (.inr w))
    | .inr (.inl f) => .inl (.inr (.inl (.inr f)))
    | .inr (.inr i) => .inr i
  invFun
    | .inl (.inl p) => .inl (.inl p)
    | .inl (.inr (.inl (.inl b))) => .inl (.inr (.inl b))
    | .inl (.inr (.inl (.inr f))) => .inr (.inl f)
    | .inl (.inr (.inr w)) => .inl (.inr (.inr w))
    | .inr i => .inr (.inr i)
  left_inv := by rintro ((p | (b | w)) | (f | i)) <;> rfl
  right_inv := by rintro ((p | ((b | f) | w)) | i) <;> rfl

def cutEnd (label : K ⊕ D → Label S)
    (partition : Bij (NodePort S D (fun d => label (.inr d))) (F ⊕ I)) :
    Bij (End S (K ⊕ D) B W label)
      (End S K (B ⊕ F) W (fun k => label (.inl k)) ⊕ I) :=
  ((cutSplit label).trans ((Bij.refl _).sum partition)).trans (cutJoin _)
def cut (g : Net S (K ⊕ D) B W)
    (partition : Bij (NodePort S D (fun d => g.label (.inr d))) (F ⊕ I))
    (closed : ∀ e i, g.wire.rename (cutEnd g.label partition) (.inl e) ≠ .inr i) :
    Net S K (B ⊕ F) W :=
  ⟨fun k => g.label (.inl k), restrict (g.wire.rename (cutEnd g.label partition)) closed⟩
 theorem cut_pairing (g : Net S (K ⊕ D) B W)
    (partition : Bij (NodePort S D (fun d => g.label (.inr d))) (F ⊕ I)) (closed) (e) :
    (cut g partition closed).wire ((cut g partition closed).wire e) = e :=
  (cut g partition closed).wire.involutive e
 theorem cut_boundary (g : Net S (K ⊕ D) B W)
    (partition : Bij (NodePort S D (fun d => g.label (.inr d))) (F ⊕ I)) (closed) (b : B) :
    cutEnd g.label partition (g.wire (.inr (.inl b))) =
      .inl ((cut g partition closed).wire (.inr (.inl (.inl b)))) := by
  have h := restrict_mate (g.wire.rename (cutEnd g.label partition)) closed
    (.inr (.inl (.inl b)))
  simpa only [Pairing.rename,cutEnd,cutSplit,cutJoin,Bij.trans,Bij.sum,Bij.refl,cut] using h
variable {V R : Type} [FiniteNames V] [FiniteNames R]
/-- A fragment can include transparent vertices on subdivided internal wires. -/
def fragmentSplit (label : K ⊕ D → Label S) :
    Bij (End S (K ⊕ D) B (W ⊕ V) label)
      (End S K B W (fun k => label (.inl k)) ⊕
        (NodePort S D (fun d => label (.inr d)) ⊕ (V × Bool))) where
  toFun
    | .inl ⟨.inl k,p⟩ => .inl (.inl ⟨k,p⟩)
    | .inl ⟨.inr d,p⟩ => .inr (.inl ⟨d,p⟩)
    | .inr (.inl b) => .inl (.inr (.inl b))
    | .inr (.inr (.inl w,d)) => .inl (.inr (.inr (w,d)))
    | .inr (.inr (.inr v,d)) => .inr (.inr (v,d))
  invFun
    | .inl (.inl ⟨k,p⟩) => .inl ⟨.inl k,p⟩
    | .inr (.inl ⟨d,p⟩) => .inl ⟨.inr d,p⟩
    | .inl (.inr (.inl b)) => .inr (.inl b)
    | .inl (.inr (.inr (w,d))) => .inr (.inr (.inl w,d))
    | .inr (.inr (v,d)) => .inr (.inr (.inr v,d))
  left_inv := by rintro (⟨k | d,p⟩ | (b | ⟨w | v,d⟩)) <;> rfl
  right_inv := by rintro ((p | (b | ⟨w,d⟩)) | (⟨n,p⟩ | ⟨v,d⟩)) <;> rfl

def fragmentEnd (label : K ⊕ D → Label S)
    (partition : Bij (NodePort S D (fun d => label (.inr d)) ⊕ (V × Bool)) (F ⊕ I)) :
    Bij (End S (K ⊕ D) B (W ⊕ V) label)
      (End S K (B ⊕ F) W (fun k => label (.inl k)) ⊕ I) :=
  ((fragmentSplit label).trans ((Bij.refl _).sum partition)).trans (cutJoin _)

def cutFragment (g : Net S (K ⊕ D) B (W ⊕ V))
    (partition : Bij (NodePort S D (fun d => g.label (.inr d)) ⊕ (V × Bool)) (F ⊕ I))
    (closed : ∀ e i, g.wire.rename (fragmentEnd g.label partition) (.inl e) ≠ .inr i) :
    Net S K (B ⊕ F) W :=
  ⟨fun k => g.label (.inl k), restrict (g.wire.rename (fragmentEnd g.label partition)) closed⟩
 theorem cutFragment_boundary (g : Net S (K ⊕ D) B (W ⊕ V))
    (partition : Bij (NodePort S D (fun d => g.label (.inr d)) ⊕ (V × Bool)) (F ⊕ I))
    (closed) (b : B) :
    fragmentEnd g.label partition (g.wire (.inr (.inl b))) =
      .inl ((cutFragment g partition closed).wire (.inr (.inl (.inl b)))) := by
  have h := restrict_mate (g.wire.rename (fragmentEnd g.label partition)) closed
    (.inr (.inl (.inl b)))
  simpa only [Pairing.rename,fragmentEnd,fragmentSplit,cutJoin,Bij.trans,Bij.sum,Bij.refl,cutFragment] using h

def Pairing.sum (p : Pairing E) (q : Pairing H) : Pairing (E ⊕ H) where
  mate := Sum.elim (Sum.inl ∘ p) (Sum.inr ∘ q)
  involutive := by rintro (e | h) <;> simp [p.involutive,q.involutive]
  fixedPointFree := by rintro (e | h) he <;> simp only [Sum.elim_inl,Sum.elim_inr,Function.comp_apply,Sum.inl.injEq,Sum.inr.injEq] at he
                       · exact p.fixedPointFree _ he
                       · exact q.fixedPointFree _ he
/-- Disjoint union plus gluing the two copies of F. No target matching is supplied. -/
def plugEnd (l : K → Label S) (r : R → Label S) :
    Bij (End S K (B ⊕ F) W l ⊕ End S R F V r)
      (End S (K ⊕ R) B ((W ⊕ V) ⊕ F) (Sum.elim l r)) where
  toFun
    | .inl (.inl ⟨k,p⟩) => .inl ⟨.inl k,p⟩
    | .inr (.inl ⟨n,p⟩) => .inl ⟨.inr n,p⟩
    | .inl (.inr (.inl (.inl b))) => .inr (.inl b)
    | .inl (.inr (.inl (.inr f))) => .inr (.inr (.inr f,false))
    | .inr (.inr (.inl f)) => .inr (.inr (.inr f,true))
    | .inl (.inr (.inr (w,d))) => .inr (.inr (.inl (.inl w),d))
    | .inr (.inr (.inr (v,d))) => .inr (.inr (.inl (.inr v),d))
  invFun
    | .inl ⟨.inl k,p⟩ => .inl (.inl ⟨k,p⟩)
    | .inl ⟨.inr n,p⟩ => .inr (.inl ⟨n,p⟩)
    | .inr (.inl b) => .inl (.inr (.inl (.inl b)))
    | .inr (.inr (.inr f,false)) => .inl (.inr (.inl (.inr f)))
    | .inr (.inr (.inr f,true)) => .inr (.inr (.inl f))
    | .inr (.inr (.inl (.inl w),d)) => .inl (.inr (.inr (w,d)))
    | .inr (.inr (.inl (.inr v),d)) => .inr (.inr (.inr (v,d)))
  left_inv := by rintro ((⟨k,p⟩ | ((b | f) | ⟨w,d⟩)) | (⟨n,p⟩ | (f | ⟨v,d⟩))) <;> rfl
  right_inv := by rintro (⟨k | n,p⟩ | (b | ⟨(w | v) | f,d⟩)) <;> try rfl
                  cases d <;> rfl

def plug (context : Net S K (B ⊕ F) W) (rhs : Net S R F V) :
    Net S (K ⊕ R) B ((W ⊕ V) ⊕ F) :=
  ⟨Sum.elim context.label rhs.label,
    (context.wire.sum rhs.wire).rename (plugEnd context.label rhs.label)⟩
 theorem plug_boundary (context : Net S K (B ⊕ F) W) (rhs : Net S R F V) (b : B) :
    (plug context rhs).wire (.inr (.inl b)) =
      plugEnd context.label rhs.label (.inl (context.wire (.inr (.inl (.inl b))))) := rfl

def replace (g : Net S (K ⊕ D) B (W ⊕ V))
    (partition : Bij (NodePort S D (fun d => g.label (.inr d)) ⊕ (V × Bool)) (F ⊕ I))
    (closed : ∀ e i, g.wire.rename (fragmentEnd g.label partition) (.inl e) ≠ .inr i)
    {T : Type} [FiniteNames T] (rhs : Net S R F T) :=
  plug (cutFragment g partition closed) rhs
 theorem replace_pairing (g : Net S (K ⊕ D) B (W ⊕ V))
    (partition : Bij (NodePort S D (fun d => g.label (.inr d)) ⊕ (V × Bool)) (F ⊕ I))
    (closed) {T : Type} [FiniteNames T] (rhs : Net S R F T) (e) :
    (replace g partition closed rhs).wire ((replace g partition closed rhs).wire e) = e :=
  (replace g partition closed rhs).wire.involutive e
 theorem replace_boundary [DecidableEq B] (g : Net S (K ⊕ D) B (W ⊕ V))
    (partition : Bij (NodePort S D (fun d => g.label (.inr d)) ⊕ (V × Bool)) (F ⊕ I))
    (closed) {T : Type} [FiniteNames T] (rhs : Net S R F T) :
    (replace g partition closed rhs).boundaryOrder = g.boundaryOrder := rfl
omit [FiniteNames J] in
/-- Restriction is natural under independent bijections of retained/deleted ends. -/
theorem restrict_natural (p : Pairing (E ⊕ I)) (q : Pairing (H ⊕ J))
    (a : Bij E H) (b : Bij I J) (cp) (cq)
    (commutes : ∀ x, (a.sum b) (p x) = q ((a.sum b) x)) (x : E) :
    a ((restrict p cp) x) = (restrict q cq) (a x) := by
  apply Sum.inl.inj (β := J)
  calc
    Sum.inl (a ((restrict p cp) x)) = (a.sum b) (.inl ((restrict p cp) x)) := rfl
    _ = (a.sum b) (p (.inl x)) := congrArg (a.sum b) (restrict_mate p cp x).symm
    _ = q ((a.sum b) (.inl x)) := commutes _
    _ = Sum.inl ((restrict q cq) (a x)) := restrict_mate q cq (a x)

theorem Pairing.transport_natural (p : Pairing E) (q : Pairing H)
    (a : Bij E H) (e : Bij E U) (f : Bij H T)
    (commutes : ∀ x, a (p x) = q (a x)) (x : U) :
    (e.symm.trans (a.trans f)) ((p.rename e) x) =
      (q.rename f) ((e.symm.trans (a.trans f)) x) := by
  change f (a (e.invFun (e (p (e.invFun x))))) =
    f (q (f.invFun (f (a (e.invFun x)))))
  simp only [e.left_inv,f.left_inv,commutes]

/-- Actual plug is compatible with corresponding renamings of both fragments.
The output renaming is induced by the same glue correspondence. -/
theorem plug_natural {K' R' W' V' : Type}
    [FiniteNames K'] [FiniteNames R'] [FiniteNames W'] [FiniteNames V']
    (c : Net S K (B ⊕ F) W) (r : Net S R F V)
    (c' : Net S K' (B ⊕ F) W') (r' : Net S R' F V')
    (a : Bij (End S K (B ⊕ F) W c.label) (End S K' (B ⊕ F) W' c'.label))
    (b : Bij (End S R F V r.label) (End S R' F V' r'.label))
    (hc : ∀ x, a (c.wire x) = c'.wire (a x))
    (hr : ∀ x, b (r.wire x) = r'.wire (b x)) (x) :
    ((plugEnd c.label r.label).symm.trans
      ((a.sum b).trans (plugEnd c'.label r'.label))) ((plug c r).wire x) =
    (plug c' r').wire (((plugEnd c.label r.label).symm.trans
      ((a.sum b).trans (plugEnd c'.label r'.label))) x) := by
  apply Pairing.transport_natural
  rintro (e | e)
  · exact congrArg Sum.inl (hc e)
  · exact congrArg Sum.inr (hr e)
end Lamping.Graph








