import Lamping.Lamping.ActionPassiveInverse
import Lamping.Lamping.UnaryActionPathShapes
namespace Lamping.AG
open Graph

private theorem fan_active_ancestor (f : Op) (i j : Nat) (lt : i<j)
    (branch : Bool) (exit : Bool⊕Aux f) (a b : Context)
    (path : LocalPath (fanRight f i j) (.inl branch) exit a b) :
    Nonempty (LocalPath (leftNet .fan f i j) (.inl branch) exit a b) := by
  obtain ⟨q,same,shape⟩ := fanRight_active_path_shape f i j branch exit path.edges a b
    path.labeling path.start path.finish
  subst exit
  have labels := path.labeling
  rw [shape] at labels
  exact ⟨⟨leftRoute .fan f i j branch q,rfl,rfl,fanAction_cross_inverse f i j lt branch q a b labels⟩⟩

/-- Every complete local fan-action RHS path, including reverse crossings and
passive application turns, has an ordinary same-A/B source path. -/
theorem fanAction_local_ancestor (f : Op) (i j : Nat) (lt : i<j)
    (entry exit : Bool⊕Aux f) (a b : Context)
    (path : LocalPath (fanRight f i j) entry exit a b) :
    Nonempty (LocalPath (leftNet .fan f i j) entry exit a b) := by
  cases entry with
  | inl branch => exact fan_active_ancestor f i j lt branch exit a b path
  | inr p =>
    cases exit with
    | inl branch =>
      obtain ⟨old⟩ := fan_active_ancestor f i j lt branch (.inr p) b a path.reverse
      exact ⟨old.reverse⟩
    | inr q =>
      rcases fanRight_passive_path_shape f i j p (.inr q) path.edges a b
        path.labeling path.start path.finish with ⟨branch,impossible,_⟩ |⟨branch,r,same,shape⟩
      · cases impossible
      · have ports : q=r := Sum.inr.inj same
        subst r
        have labels := path.labeling
        rw [shape] at labels
        exact ⟨⟨[.inr (.inl (.inr p)),.inl ⟨.inr (),.inr q⟩],rfl,rfl,
          fanAction_passive_inverse f i j branch p q a b labels⟩⟩

private theorem unary_active_ancestor (c f : Op) (single : Bij Unit (Aux c))
    (control : c=.fan ∨c=.cro ∨c=.bra) (i k j : Nat)
    (cross : ∀ q a b,Labelling (unaryRightCore c f single i k)
      [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b →
      Labelling (leftNet c f i j) (leftRoute c f i j (single ()) q) a b)
    (exit : Unit⊕Aux f) (a b : Context)
    (path : LocalPath (unaryRightCore c f single i k) (.inl ()) exit a b) :
    Nonempty (LocalPath (leftNet c f i j) (.inl (single ())) (exit.map single id) a b) := by
  obtain ⟨q,same,shape⟩ := unaryRight_active_path_shape c f single control i k exit path.edges a b
    path.labeling path.start path.finish
  subst exit
  have labels := path.labeling
  rw [shape] at labels
  exact ⟨⟨leftRoute c f i j (single ()) q,rfl,rfl,cross q a b labels⟩⟩

/-- Generic finite assembly of actual unary RHS shapes. Its local crossing
premise is discharged below by the proved cro/bra exact inverse theorems. -/
theorem unaryAction_local_ancestor (c f : Op) (single : Bij Unit (Aux c))
    (control : c=.fan ∨c=.cro ∨c=.bra) (i k j : Nat)
    (cross : ∀ q a b,Labelling (unaryRightCore c f single i k)
      [.inr (.inl (.inl ())),.inl ⟨.inl (),.inr q⟩,.inl ⟨.inr q,.inl ()⟩] a b →
      Labelling (leftNet c f i j) (leftRoute c f i j (single ()) q) a b)
    (entry exit : Unit⊕Aux f) (a b : Context)
    (path : LocalPath (unaryRightCore c f single i k) entry exit a b) :
    Nonempty (LocalPath (leftNet c f i j) (entry.map single id) (exit.map single id) a b) := by
  cases entry with
  | inl u => cases u; exact unary_active_ancestor c f single control i k j cross exit a b path
  | inr p =>
    cases exit with
    | inl u =>
      cases u
      obtain ⟨old⟩ := unary_active_ancestor c f single control i k j cross (.inr p) b a path.reverse
      exact ⟨old.reverse⟩
    | inr q =>
      rcases unaryRight_passive_path_shape c f single control i k p (.inr q) path.edges a b
        path.labeling path.start path.finish with ⟨impossible,_⟩ |⟨r,same,shape⟩
      · cases impossible
      · have ports : q=r := Sum.inr.inj same
        subst r
        have labels := path.labeling
        rw [shape] at labels
        exact ⟨⟨[.inr (.inl (.inr p)),.inl ⟨.inr (),.inr q⟩],rfl,rfl,
          unaryAction_passive_inverse c f single i k j p q a b labels⟩⟩

theorem croAction_local_ancestor (f : Op) (i j : Nat) (lt : i<j)
    (entry exit : Unit⊕Aux f) (a b : Context)
    (path : LocalPath (unaryRightCore .cro f (Bij.refl _) i (j-1)) entry exit a b) :
    Nonempty (LocalPath (leftNet .cro f i j) entry exit a b) := by
  have actual := unaryAction_local_ancestor .cro f (Bij.refl _) (Or.inr (Or.inl rfl)) i (j-1) j
    (fun q a b labels => croAction_cross_inverse f i j lt q a b labels) entry exit a b path
  simpa only [Bij.refl,Sum.map_id_id] using actual

theorem braAction_local_ancestor (f : Op) (i j : Nat) (lt : i<j)
    (entry exit : Unit⊕Aux f) (a b : Context)
    (path : LocalPath (unaryRightCore .bra f (Bij.refl _) i (j+1)) entry exit a b) :
    Nonempty (LocalPath (leftNet .bra f i j) entry exit a b) := by
  have actual := unaryAction_local_ancestor .bra f (Bij.refl _) (Or.inr (Or.inr rfl)) i (j+1) j
    (fun q a b labels => braAction_cross_inverse f i j lt q a b labels) entry exit a b path
  simpa only [Bij.refl,Sum.map_id_id] using actual
end Lamping.AG
