import Lamping.Lamping.CorridorFlow
import Lamping.Lamping.CorridorReverse
import Lamping.Lamping.ControlInteractionSchema
namespace Lamping.AG
open Graph
private theorem principal_heq {left right : Op} (same : left=right) :
    HEq (Sum.inl () : Port (.op left)) (Sum.inl () : Port (.op right)) := by
  cases same; rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {boundary : B → Bool}

/-- Exact principal label compatibility, including a reversed orientation,
constructs a physical schema step on the supplied actual corridor. -/
theorem Schema.FitsControlPair.graph_step {schema : Schema} {left right : Op} {i j : Nat}
    (fit : schema.FitsControlPair left right i j)
    (flow : FlowBalance g boundary) (route : TransparentCorridor g) (ln rn : N)
    (ll : g.label ln=label left i) (rl : g.label rn=label right j)
    (lp : Port (g.label ln).sort) (rp : Port (g.label rn).sort)
    (lh : HEq lp (Sum.inl () : Port (.op left)))
    (rh : HEq rp (Sum.inl () : Port (.op right)))
    (first : route.first=⟨ln,lp⟩) (last : route.last=⟨rn,rp⟩) :
    ∃ target : ActualNet B,GraphStep schema (ActualNet.ofNet g) target := by
  rcases fit with ⟨active,passive,low,high⟩ |⟨active,passive,low,high⟩
  · exact physical_corridor_graph_step_of_flow g schema flow route ln rn
      (by rw [active,low]; exact ll) (by rw [passive,high]; exact rl) lp rp
      (lh.trans (principal_heq active.symm)) (rh.trans (principal_heq passive.symm)) first last
  · exact physical_corridor_graph_step_of_flow g schema flow route.reverse rn ln
      (by rw [active,low]; exact rl) (by rw [passive,high]; exact ll) rp lp
      (rh.trans (principal_heq active.symm)) (lh.trans (principal_heq passive.symm)) last first

/-- Two controls on an actually labelled principal connection admit an actual
standard rewrite, including W subdivisions and either index orientation. -/
theorem control_corridor_graph_step {left right : Op} {i j : Nat}
    (leftControl : left=.fan ∨left=.cro ∨left=.bra)
    (rightControl : right=.fan ∨right=.cro ∨right=.bra)
    {p : Port (.op left)} {q : Port (.op right)} {a b c : Context}
    (leftTurn : Traversal i (.op left) p (.inl ()) a b)
    (rightTurn : Traversal j (.op right) (.inl ()) q b c)
    (flow : FlowBalance g boundary) (route : TransparentCorridor g) (ln rn : N)
    (ll : g.label ln=label left i) (rl : g.label rn=label right j)
    (lp : Port (g.label ln).sort) (rp : Port (g.label rn).sort)
    (lh : HEq lp (Sum.inl () : Port (.op left)))
    (rh : HEq rp (Sum.inl () : Port (.op right)))
    (first : route.first=⟨ln,lp⟩) (last : route.last=⟨rn,rp⟩) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  obtain ⟨schema,fit⟩ := Traversal.control_pair_schema leftControl rightControl leftTurn rightTurn
  obtain ⟨target,step⟩ := fit.graph_step flow route ln rn ll rl lp rp lh rh first last
  exact ⟨schema,target,step⟩

/-- A lower-index control facing any standard operator principal has the
actual corresponding action rule, rather than a hypothetical interaction. -/
theorem low_control_corridor_graph_step {control passive : Op} {i j : Nat}
    (kind : control=.fan ∨control=.cro ∨control=.bra) (lower : i<j)
    (flow : FlowBalance g boundary) (route : TransparentCorridor g) (ln rn : N)
    (ll : g.label ln=label control i) (rl : g.label rn=label passive j)
    (lp : Port (g.label ln).sort) (rp : Port (g.label rn).sort)
    (lh : HEq lp (Sum.inl () : Port (.op control)))
    (rh : HEq rp (Sum.inl () : Port (.op passive)))
    (first : route.first=⟨ln,lp⟩) (last : route.last=⟨rn,rp⟩) :
    ∃ schema target,GraphStep schema (ActualNet.ofNet g) target := by
  have compatible : ∃ schema : Schema,schema.FitsControlPair control passive i j := by
    rcases kind with same |same |same <;> subst control
    · exact ⟨.fanAction passive i j lower,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
    · exact ⟨.croAction passive i j lower,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
    · exact ⟨.braAction passive i j lower,Or.inl ⟨rfl,rfl,rfl,rfl⟩⟩
  obtain ⟨schema,fit⟩ := compatible
  obtain ⟨target,step⟩ := fit.graph_step flow route ln rn ll rl lp rp lh rh first last
  exact ⟨schema,target,step⟩

/-- Equal-index application/lambda principals on the actual corridor give a
real graph beta step, with no source Matches or soundness premise. -/
theorem beta_corridor_graph_step {i : Nat} (flow : FlowBalance g boundary)
    (route : TransparentCorridor g) (app lam : N)
    (appLabel : g.label app=label .app i) (lamLabel : g.label lam=label .lam i)
    (ap : Port (g.label app).sort) (lp : Port (g.label lam).sort)
    (ah : HEq ap (Sum.inl () : Port (.op .app)))
    (lh : HEq lp (Sum.inl () : Port (.op .lam)))
    (first : route.first=⟨app,ap⟩) (last : route.last=⟨lam,lp⟩) :
    ∃ target,GraphStep (.beta i) (ActualNet.ofNet g) target :=
  physical_corridor_graph_step_of_flow g (.beta i) flow route app lam
    appLabel lamLabel ap lp ah lh first last
end
end Lamping.AG
