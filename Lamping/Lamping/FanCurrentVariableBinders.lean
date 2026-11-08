import Lamping.Lamping.ActionCopiedTransparency
import Lamping.Lamping.MatchingSourceBinders
import Lamping.Lambda.PrerequisitePrefixes
namespace Lamping.AG
open Graph Lambda Lambda.Labelled
private def currentDepartureToken : (kind : Kind)→Port kind→Path
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []
private theorem current_body_token {kind : Kind} (port : Port kind)
    (shape : kind=.op .lam) (role : HEq port lamBody) : currentDepartureToken kind port=[.body] := by
  subst kind
  cases eq_of_heq role
  rfl
private theorem current_context_kind {kind : Kind} (ctx : Port kind)
    (shape : kind=.op .lam) (role : HEq ctx (Sum.inl () : Port (.op .lam))) :
    portKind kind ctx=some .lam := by
  subst kind
  cases eq_of_heq role
  rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {current : LTerm} {g : Net signature N B W} {root : B}

/-- The real matched variable decomposition is anchored at the specified
CURRENT lexical binder coordinate, without label or physical-node injectivity. -/
theorem Matches.current_lexical_binding_access
    (matching : Matches g root current.erase)
    (atVariable : current.subterm leafPath=some (.var stamp index))
    (lexical : leafPath=parentPath++(.body::rest)) (depth : index=binderDepth rest)
    (leaf parent : RootAccess g root)
    (leafWord : accessWord g leaf.val=leafPath) (parentWord : accessWord g parent.val=parentPath) :
    ∃ (loop : List (Endpoint g)) (a b c : Context) (binding : BindingLoop g loop b c) (ctx : Port (g.label binding.binder).sort),
      leaf.val=parent.val++loop ∧accessWord g loop=rest ∧
      HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      parent.val.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)) ∧
      Labelling g parent.val a b := by
  have atWord : subtermAt current.erase (accessWord g leaf.val)=some (.var index) := by
    rw [leafWord,←LTerm.erase_subterm,atVariable];rfl
  obtain ⟨chosen,loop,a,b,c,binding,ctx,_body,split,ctxRole,finish,labels,_lookup,words,actualDepth⟩ :=
    matching.variable_binding_access leaf atWord
  have same := binding_prefix_depth_unique
    (words.symm.trans (leafWord.trans lexical)) (actualDepth.symm.trans depth)
  have parentEq : chosen=parent := matching.accessWord_injective (same.1.trans parentWord.symm)
  rw [parentEq] at split finish labels
  exact ⟨loop,a,b,c,binding,ctx,split,same.2,ctxRole,finish,labels⟩

/-- An already supplied SAME-whole binding loop has THIS current lexical
parent prefix. The loop and assignments are inputs from actual transparency,
not a desired parent profile or a completed partial path. -/
theorem Matches.current_binding_loop_prefix
    (matching : Matches g root current.erase)
    (atVariable : current.subterm leafPath=some (.var stamp index))
    (lexical : leafPath=parentPath++(.body::rest)) (depth : index=binderDepth rest)
    (leaf parent : RootAccess g root)
    (leafWord : accessWord g leaf.val=leafPath) (parentWord : accessWord g parent.val=parentPath)
    (pre loop : List (Endpoint g)) (a seam b : Context)
    (binding : BindingLoop g loop seam b) (ctx : Port (g.label binding.binder).sort)
    (ctxRole : HEq ctx (Sum.inl () : Port (.op .lam)))
    (split : leaf.val=pre++loop)
    (finish : pre.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)))
    (labels : Labelling g pre a seam) : pre=parent.val ∧accessWord g loop=rest := by
  have nonempty : pre≠[] := by intro empty;rw [empty] at finish;cases finish
  have rooted : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (nonempty rfl)
    | cons e es => simpa only [split,List.cons_append,List.head?_cons] using leaf.property.2.1
  have kind : accessKind g pre=some .lam := by
    unfold accessKind
    rw [finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact current_context_kind ctx binding.isLam ctxRole
  have forward : Forward g pre := by
    have actual := leaf.property.1.2
    rw [split] at actual
    exact actual.prefix_of_append nonempty
  let prefixAccess : RootAccess g root := ⟨pre,⟨⟨⟨a,seam,labels⟩,forward⟩,rooted,⟨.lam,kind⟩⟩⟩
  have suffix : BindingSuffix g leaf.val (binderDepth (accessWord g loop)) :=
    ⟨pre,loop,a,seam,b,binding,ctx,split,ctxRole,finish,labels,rfl⟩
  have matchingCopy := matching
  obtain ⟨bijection,corresponds,_⟩ := matchingCopy
  obtain ⟨atPosition,u,lookup,observes⟩ := corresponds leaf
  have atWord : subtermAt current.erase (accessWord g leaf.val)=some (.var index) := by
    rw [leafWord,←LTerm.erase_subterm,atVariable];rfl
  rw [←atPosition] at lookup
  have shape : u=.var index := Option.some.inj (lookup.symm.trans atWord)
  subst u
  have actualDepth : binderDepth (accessWord g loop)=index := observes.2.2 _ suffix
  have words : accessWord g leaf.val=accessWord g pre++(.body::accessWord g loop) := by
    rw [split,accessWord_append g pre loop nonempty]
    obtain ⟨tail,loopEq⟩ := List.head?_eq_some_iff.mp binding.start
    rw [loopEq]
    have token : arrivalWord g (.inl ⟨binding.binder,binding.body⟩)=[.body] :=
      current_body_token binding.body binding.isLam binding.body_role
    simp only [List.flatMap_cons,token,List.singleton_append,accessWord]
  have coordinates := binding_prefix_depth_unique
    (words.symm.trans (leafWord.trans lexical)) (actualDepth.trans depth)
  have same : prefixAccess=parent := matching.accessWord_injective (coordinates.1.trans parentWord.symm)
  exact ⟨congrArg Subtype.val same,coordinates.2⟩
end
section
variable {K B W V : Type} [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K→Label signature} {i j : Nat} {lt : i<j}
variable (site : PathSite (.fanAction .lam i j lt) kept (B:=B) (W:=W) (V:=V))

/-- Existing physical same-copy transparency is reused once. New information
is the specified CURRENT syntax binder, its literal parent RootAccess and
its actual zero-edge jump/next successful chain read, under SAME whole labels. -/
theorem PathSite.fan_current_variable_binder
    {current : LTerm} {root : B} {boundary : B→Bool}
    (matching : Matches site.reduce root current.erase)
    (flow : FlowBalance site.net boundary) (positive : boundary root=true)
    (oldT : Transparency site.net root)
    (atVariable : current.subterm leafPath=some (.var stamp index))
    (binderLookup : current.subterm parentPath=some (.lam origin body))
    (lexical : leafPath=parentPath++(.body::rest)) (depth : index=binderDepth rest)
    (leaf parent : RootAccess site.reduce root)
    (leafWord : accessWord site.reduce leaf.val=leafPath)
    (parentWord : accessWord site.reduce parent.val=parentPath)
    (branch : Bool)
    (bindingFinish : leaf.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),lamBind⟩)))
    {a b : Context} (whole : Labelling site.reduce leaf.val a b)
    (next : PrerequisiteChain current parentPath edges) :
    ∃ (loop : List (Endpoint site.reduce)) (seam : Context) (binding : BindingLoop site.reduce loop seam b),
      leaf.val=parent.val++loop ∧binding.binder=.inr (.inl branch) ∧
      accessWord site.reduce loop=rest ∧
      parent.val.getLast?=some (site.reduce.wire (.inl ⟨.inr (.inl branch),.inl ()⟩)) ∧
      Labelling site.reduce parent.val a seam ∧
      PrerequisitePrefix current leafPath [] parentPath ∧
      PrerequisiteChain current leafPath edges ∧edges.head?=some parentPath ∧
      PrerequisiteReads current parentPath parentPath := by
  obtain ⟨pre,loop,seam,binding,split,binderEq,finish,labels⟩ :=
    site.fan_copied_lambda_transparency flow root positive oldT whole leaf.property.2.1 branch bindingFinish
  rcases binding with ⟨node,sort,bodyPort,bindPort,bodyRole,bindRole,start,ending,loopLabels,loopForward,shell⟩
  dsimp at binderEq
  subst node
  let actualBinding : BindingLoop site.reduce loop seam b :=
    ⟨.inr (.inl branch),sort,bodyPort,bindPort,bodyRole,bindRole,start,ending,loopLabels,loopForward,shell⟩
  have same := matching.current_binding_loop_prefix atVariable lexical depth leaf parent leafWord parentWord
    pre loop a seam b actualBinding (.inl ()) HEq.rfl split finish labels
  rw [same.1] at split finish labels
  have jump : PrerequisitePrefix current leafPath [] parentPath :=
    .var atVariable binderLookup lexical depth .refl
  have nextRead : edges.head?=some parentPath := by
    rcases next.lambda_cases binderLookup with ⟨_,_,_,_,_,equal⟩|⟨_,_,_,_,_,equal,_⟩ <;> rw [equal] <;> rfl
  exact ⟨loop,seam,actualBinding,split,rfl,same.2,finish,labels,jump,
    jump.close next,nextRead,Or.inr ⟨origin,body,binderLookup,rfl⟩⟩
end
end Lamping.AG
#print axioms Lamping.AG.Matches.current_lexical_binding_access
#print axioms Lamping.AG.Matches.current_binding_loop_prefix
#print axioms Lamping.AG.PathSite.fan_current_variable_binder