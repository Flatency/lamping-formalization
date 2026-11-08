import Lamping.Lamping.RootPathInputs
import Lamping.Lamping.ForwardAccessPrefixes
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Root-input existence suffices to compare two existing accesses using one
common assignment. No arbitrary non-root source input is required. -/
theorem RootInputs.accessWord_injective (inputs : RootInputs g root) :
    Function.Injective (fun path : RootAccess g root => accessWord g path.val) := by
  intro first second word
  obtain ⟨b,left⟩ := inputs.access first Context.empty
  obtain ⟨c,right⟩ := inputs.access second Context.empty
  apply Subtype.ext
  exact left.forward_access_word_unique first.property.1.2 right second.property.1.2
    (first.property.2.1.trans second.property.2.1.symm) word first.property.2.2 second.property.2.2

/-- Prefix reflection concerns two supplied actual rooted accesses, with
their literal edge occurrences retained. It constructs no extra continuation. -/
theorem RootInputs.accessWord_prefix (inputs : RootInputs g root)
    (short long : RootAccess g root) (suffix : Path)
    (word : accessWord g long.val=accessWord g short.val++suffix) :
    ∃ tail,long.val=short.val++tail := by
  obtain ⟨b,left⟩ := inputs.access short Context.empty
  obtain ⟨d,right⟩ := inputs.access long Context.empty
  exact left.forward_access_prefix short.property.1.2 right long.property.1.2
    (short.property.2.1.trans long.property.2.1.symm) suffix word short.property.2.2 long.property.2.2
end
end Lamping.AG
