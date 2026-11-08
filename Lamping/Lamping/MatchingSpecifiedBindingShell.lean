import Lamping.Lamping.HistoryTypedBinders
import Lamping.Lamping.ExpandedInvariantBase
import Lamping.Lamping.GlobalPathInvariants
import Lamping.Lamping.MatchingSourceBinders
import Lamping.Lamping.PathLabelDeterminism
namespace Lamping.AG
open Graph Lambda
private theorem lambda_kind (kind : Kind) (ctx : Port kind)
    (shape : kind=.op .lam) (role : HEq ctx (Sum.inl () : Port (.op .lam))) :
    portKind kind ctx=some .lam := by
  subst kind
  cases eq_of_heq role
  rfl
private def departureToken : (kind : Kind) → Port kind → Path
  | .op .app, .inl () => [.fn]
  | .op .app, .inr true => [.arg]
  | .op .lam, .inr true => [.body]
  | _,_ => []
private theorem lambda_token (kind : Kind) (body : Port kind)
    (shape : kind=.op .lam) (role : HEq body lamBody) :
    departureToken kind body=[.body] := by
  subst kind
  cases eq_of_heq role
  rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {t : Term}

/-- Source transparency selects an actual assigned loop. The syntax index
identifies its literal parent occurrence, so its seam is the supplied parent's
seam under the SAME input. No shell is assumed for either path. -/
theorem Matches.specified_binding_shell
    (matching : Matches g root t) (transparency : Transparency g root)
    (parent leaf : RootAccess g root) (p q : Path)
    (parentWord : accessWord g parent.val=p)
    (leafWord : accessWord g leaf.val=p++(.body::q))
    (atLeaf : subtermAt t (p++(.body::q))=some (.var (binderDepth q)))
    (node : N) (ctx body bind : Port (g.label node).sort)
    (sort : (g.label node).sort=.op .lam)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (bodyRole : HEq body lamBody) (bindRole : HEq bind lamBind)
    (leafEnd : leaf.val.getLast?=some (g.wire (.inl ⟨node,bind⟩)))
    {input seam output : Context}
    (whole : Labelling g leaf.val input output)
    (before : Labelling g parent.val input seam) :
    Context.SameShell (g.label node).index seam output := by
  obtain ⟨pre,loop,middle,binding,split,sameBinder,preEnd,preLabels⟩ :=
    transparency leaf.val input output node ctx body bind sort ctxRole bodyRole bindRole
      leaf.property.2.1 leafEnd leaf.property.1.2 whole
  subst node
  let actualCtx := ctx
  have actualRole : HEq actualCtx (Sum.inl () : Port (.op .lam)) := ctxRole
  have actualEnd : pre.getLast?=some (g.wire (.inl ⟨binding.binder,actualCtx⟩)) := preEnd
  have suffix : BindingSuffix g leaf.val (binderDepth (accessWord g loop)) :=
    ⟨pre,loop,input,middle,output,binding,actualCtx,split,actualRole,actualEnd,preLabels,rfl⟩
  have matchingCopy := matching
  obtain ⟨bijection,corresponds,_⟩ := matchingCopy
  obtain ⟨word,sub,lookup,observes⟩ := corresponds leaf
  have leafLookup : subtermAt t (accessWord g leaf.val)=some (.var (binderDepth q)) := by
    rw [leafWord]
    exact atLeaf
  rw [←word] at lookup
  have shape : sub=.var (binderDepth q) := Option.some.inj (lookup.symm.trans leafLookup)
  subst sub
  have depth : binderDepth (accessWord g loop)=binderDepth q := observes.2.2 _ suffix
  have preNonempty : pre≠[] := by intro empty; rw [empty] at actualEnd; cases actualEnd
  have preRoot : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (preNonempty rfl)
    | cons e es => simpa only [split,List.cons_append,List.head?_cons] using leaf.property.2.1
  have kind : accessKind g pre=some .lam := by
    unfold accessKind
    rw [actualEnd]
    simp only [Option.bind_some,Pairing.involutive]
    exact lambda_kind _ actualCtx binding.isLam actualRole
  have preForward : Forward g pre := by
    have forward := leaf.property.1.2
    rw [split] at forward
    exact forward.prefix_of_append preNonempty
  let chosen : RootAccess g root := ⟨pre,⟨⟨⟨input,middle,preLabels⟩,preForward⟩,preRoot,⟨_,kind⟩⟩⟩
  have bodyToken : arrivalWord g (.inl ⟨binding.binder,binding.body⟩)=[.body] := by
    change departureToken (g.label binding.binder).sort binding.body=[.body]
    exact lambda_token _ _ binding.isLam binding.body_role
  have words : accessWord g leaf.val=accessWord g pre++(.body::accessWord g loop) := by
    rw [split,accessWord_append g pre loop preNonempty]
    obtain ⟨tail,loopEq⟩ := List.head?_eq_some_iff.mp binding.start
    rw [loopEq]
    simp only [List.flatMap_cons,bodyToken,List.singleton_append,accessWord]
  have paths := words.symm.trans leafWord
  have occurrence := binding_prefix_depth_unique paths depth
  have chosenEq : chosen=parent := matching.accessWord_injective (occurrence.1.trans parentWord.symm)
  have preEq : pre=parent.val := congrArg Subtype.val chosenEq
  have seamEq : middle=seam := (preEq ▸ preLabels).output_unique before
  simpa only [seamEq] using binding.shell

/-- Zero actual events for the typed binder invariant. Arbitrary supplied
paired streams are ordinary on this original source word; no restriction on
their count, no full Independence and no desired shell is assumed. -/
theorem Matches.typed_syntax_binders {original : Lambda.Labelled.LTerm}
    (matching : Matches g root original.erase) (initial : Lambda.Labelled.INIT original)
    (transparency : Transparency g root)
    (selection : SourceEdgeSelection original g root) (beta : BetaEdge g) :
    TypedSyntaxBinders selection beta original := by
  intro p stamp body atLambda q atVariable ambient loop binder ctx ambientEval leafEval
    sort role ambientEnd input output seam count blocks prefixLabels
  obtain ⟨parent,leaf,oldLoop,a,b,c,binding,oldCtx,parentWord,leafWord,split,_loopWord,
      _labels,oldRole,finish,parentEval,oldLeafEval,_support,_parentGen,_leafGen⟩ :=
    matching.original_supported_loop initial selection beta atLambda atVariable
  have sameAmbient : ambient=parent.val := Option.some.inj (ambientEval.symm.trans parentEval)
  have sameWhole : ambient++loop=leaf.val := Option.some.inj (leafEval.symm.trans oldLeafEval)
  rw [sameAmbient] at ambientEnd
  have wires := Option.some.inj (finish.symm.trans ambientEnd)
  have ports := congrArg g.wire.mate wires
  simp only [Pairing.involutive] at ports
  have sameBinder : binding.binder=binder := congrArg Sigma.fst (Sum.inl.inj ports)
  have wholeOrdinary : Labelling g leaf.val input output := by
    have actual := blocks.labelling g
    rw [sameWhole] at actual
    exact actual.ordinary_of_forward g leaf.property.1.2
  have prefixOrdinary : Labelling g parent.val input seam := by
    rw [sameAmbient] at prefixLabels
    exact prefixLabels.ordinary_of_forward g parent.property.1.2
  have atLeaf : subtermAt original.erase (p++(.body::q))=some (.var (binderDepth q)) := by
    rw [subtermAt_append,←Lambda.Labelled.LTerm.erase_subterm,atLambda]
    exact atVariable
  have leafEnd : leaf.val.getLast?=some (g.wire (.inl ⟨binding.binder,binding.bind⟩)) := by
    rw [split,List.getLast?_append,binding.finish,Option.some_or]
  have shell := matching.specified_binding_shell transparency parent leaf p q parentWord leafWord atLeaf
    binding.binder oldCtx binding.body binding.bind binding.isLam oldRole binding.body_role binding.bind_role
    leafEnd wholeOrdinary prefixOrdinary
  simpa only [sameBinder] using shell
end
end Lamping.AG




