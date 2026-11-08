import Lamping.Lamping.MatchingFirstInsertionCoherence
import Lamping.Lambda.ContractumPositionOrigins
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- Every position of the FIRST local syntax contractum has its actual old
origin and an actual coherent physical source image for all root inputs.
This does not claim one local syntax contraction exhausts a graph beta fiber. -/
theorem ActualRedexAccess.first_contractum_coherent_positions
    {t : Term} {redex : RedexOcc t} (source : ActualRedexAccess g root redex)
    (matching : Matches g root t) (inputs : RootInputs g root)
    {boundary : B → Bool} (flow : FlowBalance g boundary) (positive : boundary root=true)
    {heights : B → Int} (balance : IndexedLevelBalance g heights) (rootDepth : heights root=0)
    (transparency : Transparency g root) (beta : BetaEdge g)
    (app : source.connection.app=beta.app) (lam : source.connection.lam=beta.lam)
    (principal : source.connection.edges=beta.principal)
    {body argument : Term} (lookup : subtermAt t redex.val=some (.app (.lam body) argument))
    (position : Position (contract body argument)) :
    (∃ (old : Term) (access : RootAccess g root),
      subtermAt body position.val=some old ∧
      accessWord g access.val=(redex.val++[.fn,.body])++position.val ∧
      ∀ requested : Context,∃ output,CoherentExpandedCore g root access.val requested output) ∨
    (∃ (q r : Path) (descendant : RootAccess g root) (loop suffix : List (Endpoint g)),
      position.val=q++r ∧ArgumentOccurrence body q ∧
      accessWord g descendant.val=(redex.val++[.arg])++r ∧
      descendant.val=source.parent.val++beta.argEnd::suffix ∧accessWord g loop=q ∧
      ∀ requested : Context,∃ output,CoherentExpandedCore g root
        (source.parent.val++beta.principal++loop++beta.reverseRoute++[beta.argEnd]++suffix) requested output) := by
  have retained : ∀ old,subtermAt body position.val=some old →
      ∃ access : RootAccess g root,
        accessWord g access.val=(redex.val++[.fn,.body])++position.val ∧
        ∀ requested : Context,∃ output,CoherentExpandedCore g root access.val requested output := by
    intro old atOld
    have valid : subtermAt t ((redex.val++[.fn,.body])++position.val)=some old := by
      simp only [subtermAt_append,lookup,Option.bind_some,subtermAt,atOld]
    let sourcePosition : Position t := ⟨(redex.val++[.fn,.body])++position.val,by rw [valid]; rfl⟩
    obtain ⟨access,word,_⟩ := Matches.observation g matching sourcePosition
    refine ⟨access,word,?_⟩
    intro requested
    obtain ⟨output,labels⟩ := inputs.access access requested
    exact ⟨output,.base labels access.property.1.2 access.property.2.1⟩
  obtain ⟨target,atTarget⟩ : ∃ target,subtermAt (contract body argument) position.val=some target := by
    cases found : subtermAt (contract body argument) position.val with
    | none => have impossible := position.property; rw [found] at impossible; cases impossible
    | some target => exact ⟨target,rfl⟩
  rcases subtermAt_contract_origins atTarget with
    ⟨old,atOld,_,_⟩ | ⟨k,j,atOld,_,_,_⟩ | ⟨q,r,split,occurs,copyLookup⟩
  · obtain ⟨access,word,coherent⟩ := retained old atOld
    exact Or.inl ⟨old,access,atOld,word,coherent⟩
  · obtain ⟨access,word,coherent⟩ := retained (.var k) atOld
    exact Or.inl ⟨.var k,access,atOld,word,coherent⟩
  · have validArgument : subtermAt argument r≠none := by
      intro missing
      rw [subtermAt_rename,missing] at copyLookup
      cases copyLookup
    let argPosition : Position argument := ⟨r,by
      cases found : subtermAt argument r with
      | none => exact False.elim (validArgument found)
      | some _ => rfl⟩
    obtain ⟨descendant,loop,suffix,a,b,binding,word,argSplit,loopWord,_binder,coherent⟩ :=
      source.coherent_argument_position matching inputs flow positive balance rootDepth transparency
        beta app lam principal lookup q occurs argPosition
    exact Or.inr ⟨q,r,descendant,loop,suffix,split,occurs,word,argSplit,loopWord,coherent⟩
end
end Lamping.AG
