import Lamping.Lamping.MatchingDefinitions
import Lamping.Lamping.Encoding
import Lamping.Lamping.InitialAccessWords
import Lamping.Lamping.InitialAccessDeterminism
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)

/-- Source-geometry assembly lemma. Each of the three premises is a separate
path-classification obligation; this theorem does not assert they hold on an
encoding or a reachable graph. Prefix preservation follows from physical words. -/
theorem matches_of_access_classification (root : B) (t : Term)
    (visible : ∀ es : RootAccess g root,
      ∃ u, subtermAt t (accessWord g es.val) = some u ∧ Observes g es.val (syntaxShape u))
    (covers : ∀ p : Position t,
      ∃ es : RootAccess g root, accessWord g es.val = p.val)
    (injectiveWord : ∀ es fs : RootAccess g root,
      accessWord g es.val = accessWord g fs.val → es = fs) : Matches g root t := by
  classical
  let forward : RootAccess g root → Position t := fun es =>
    ⟨accessWord g es.val, by obtain ⟨u,hu,_⟩ := visible es; simp only [hu,Option.isSome_some]⟩
  let backward : Position t → RootAccess g root := fun p => Classical.choose (covers p)
  have backWord (p : Position t) : accessWord g (backward p).val = p.val :=
    Classical.choose_spec (covers p)
  let f : Bij (RootAccess g root) (Position t) := {
    toFun := forward
    invFun := backward
    left_inv := by
      intro es
      apply injectiveWord
      exact backWord (forward es)
    right_inv := by
      intro p
      exact Subtype.ext (backWord p) }
  refine ⟨f,?_,?_⟩
  · intro es
    exact ⟨rfl,visible es⟩
  · intro es fs hp
    obtain ⟨suffix,he⟩ := hp
    refine ⟨suffix.flatMap (arrivalWord g),?_⟩
    change accessWord g fs.val = accessWord g es.val ++ _
    rw [he]
    apply accessWord_append g es.val suffix
    intro hn
    have hr := es.property.2.1
    rw [hn] at hr
    cases hr
end

/-- Assembly at the actual encoding after the two remaining source geometry
classifications have been proved. Word injectivity is already a theorem. -/
theorem encode_matches_of_access_classification (t : Term) (n : Nat)
    (visible : ∀ es : RootAccess (encode n t).net (.inl ()),
      ∃ u, subtermAt t (accessWord (encode n t).net es.val) = some u ∧
        Observes (encode n t).net es.val (syntaxShape u))
    (covers : ∀ p : Position t,
      ∃ es : RootAccess (encode n t).net (.inl ()), accessWord (encode n t).net es.val = p.val) :
    Matches (encode n t).net (.inl ()) t :=
  matches_of_access_classification _ _ _ visible covers (encode_accessWord_injective t n)
end Lamping.AG

