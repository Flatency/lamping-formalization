import Lamping.Lamping.MatchingNestedGeneratedBase
import Lamping.Lambda.NestedBinderCoordinates
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

/-- In a REAL inner-first, outer-second contraction, an outer-bound variable
inside an inner argument copy supplies its ORIGINAL ordinary binding loop.
The old leaf and every physical common-prefix/generation fact are derived. -/
theorem ActualRedexAccess.nested_history_generated
    {t : Term} {outerRedex innerRedex : RedexOcc t}
    (outerSource : ActualRedexAccess g root outerRedex)
    (innerSource : ActualRedexAccess g root innerRedex)
    (matching : Matches g root t) (outer inner : BetaEdge g)
    (outerApp : outerSource.connection.app=outer.app)
    (outerLam : outerSource.connection.lam=outer.lam)
    (outerPrincipal : outerSource.connection.edges=outer.principal)
    (innerApp : innerSource.connection.app=inner.app)
    (innerLam : innerSource.connection.lam=inner.lam)
    (innerPrincipal : innerSource.connection.edges=inner.principal)
    {body argument innerBody innerArgument after : Term}
    (outerLookup : subtermAt t outerRedex.val=some (.app (.lam body) argument))
    (innerLookup : subtermAt t innerRedex.val=some (.app (.lam innerBody) innerArgument))
    (y z q : Path)
    (nestedAt : innerRedex.val=(outerRedex.val++[.fn,.body])++y)
    (innerStep : BetaAt body y after)
    (innerVariable : ArgumentOccurrence innerBody q)
    (currentVariable : subtermAt after (y++(q++z))=some (.var (binderDepth (y++(q++z))))) :
    BetaHistory [[.fn,.body]++y,[]] (.app (.lam body) argument) (contract after argument) ∧
    ∃ (pre loop tail suffix : List (Endpoint g)),
      innerSource.parent.val=(outerSource.parent.val++outer.principal)++pre ∧
      GeneratedExpandedBindingLoop g root (outerSource.parent.val++outer.principal) outer.lam
        (pre++inner.principal++loop++inner.reverseRoute++[inner.argEnd]++tail) ∧
      GeneratedExpandedProperPath g root
        (outerSource.parent.val++outer.principal++
          (pre++inner.principal++loop++inner.reverseRoute++[inner.argEnd]++tail)++
          outer.reverseRoute++[outer.argEnd]++suffix) := by
  have bodyLookup : subtermAt t (outerRedex.val++[.fn,.body])=some body := by
    simp only [subtermAt_append,outerLookup,Option.bind_some,subtermAt]
  have innerLocalLookup : subtermAt body y=some (.app (.lam innerBody) innerArgument) := by
    rw [nestedAt,subtermAt_append,bodyLookup,Option.bind_some] at innerLookup
    exact innerLookup
  have oldArgument := (innerStep.nested_copied_outer_variable_iff innerLocalLookup innerVariable z).mp currentVariable
  have outerVariable : subtermAt body (y++(.arg::z))=some (.var (binderDepth (y++(.arg::z)))) := by
    rw [subtermAt_append,innerLocalLookup,Option.bind_some]
    simpa only [subtermAt,binderDepth_append,binderDepth] using oldArgument
  have generated := outerSource.nested_generated_base innerSource matching outer inner
    outerApp outerLam outerPrincipal innerApp innerLam innerPrincipal outerLookup innerLookup
    y z q nestedAt outerVariable innerVariable
  refine ⟨?_,generated⟩
  obtain ⟨b,a,atRedex,replaced⟩ := innerStep
  have lifted : BetaAt (.app (.lam body) argument) ([.fn,.body]++y)
      (.app (.lam after) argument) := by
    refine ⟨b,a,atRedex,?_⟩
    change ((replaceAt body y (contract b a)).map Term.lam).map (fun f => Term.app f argument)=
      some (.app (.lam after) argument)
    rw [replaced]
    rfl
  exact .cons lifted (.cons ⟨after,argument,rfl,rfl⟩ (.nil _))
end
end Lamping.AG

