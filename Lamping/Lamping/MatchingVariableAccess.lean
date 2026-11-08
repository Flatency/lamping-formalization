import Lamping.Lamping.MatchingSubtermAccess
namespace Lamping.AG
open Graph Lambda
private theorem lambda_context_kind (kind : Kind) (ctx : Port kind)
    (shape : kind=.op .lam) (role : HEq ctx (Sum.inl () : Port (.op .lam))) :
    portKind kind ctx=some .lam := by
  subst kind
  have eq : ctx=.inl () := eq_of_heq role
  subst ctx
  rfl
private def departureToken : (kind : Kind) → Port kind → Path
  | .op .app, .inl () => [.fn]
  | .op .app, .inr true => [.arg]
  | .op .lam, .inr true => [.body]
  | _, _ => []
private theorem lambda_body_word (kind : Kind) (body : Port kind)
    (shape : kind=.op .lam) (role : HEq body lamBody) :
    departureToken kind body=[.body] := by
  subst kind
  have eq : body=lamBody := eq_of_heq role
  subst body
  rfl
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}
/-- The original literal binding suffix determines a proper rooted prefix at
that same physical lambda context, retaining its original labelling. -/
theorem RootAccess.binding_prefix (access : RootAccess g root) {k : Nat}
    (suffix : BindingSuffix g access.val k) :
    ∃ (parent : RootAccess g root) (loop : List (Endpoint g)) (a b c : Context)
      (binding : BindingLoop g loop b c) (ctx : Port (g.label binding.binder).sort),
      access.val=parent.val++loop ∧
      HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      parent.val.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)) ∧
      Labelling g parent.val a b ∧ accessKind g parent.val=some .lam ∧
      accessWord g access.val=accessWord g parent.val++(.body::accessWord g loop) ∧
      k=binderDepth (accessWord g loop) := by
  obtain ⟨pre,loop,a,b,c,binding,ctx,split,role,finish,labels,depth⟩ := suffix
  have nonempty : pre≠[] := by intro eq; simp [eq] at finish
  have preRoot : pre.head?=some (.inr (.inl root)) := by
    cases pre with
    | nil => exact False.elim (nonempty rfl)
    | cons e pre => simpa only [split,List.cons_append,List.head?_cons] using access.property.2.1
  have forward := access.property.1.2
  rw [split] at forward
  have kind : accessKind g pre=some .lam := by
    unfold accessKind
    rw [finish]
    simp only [Option.bind_some,Pairing.involutive]
    exact lambda_context_kind _ _ binding.isLam role
  let parent : RootAccess g root := ⟨pre,⟨⟨⟨a,b,labels⟩,forward.prefix_of_append nonempty⟩,preRoot,⟨_,kind⟩⟩⟩
  refine ⟨parent,loop,a,b,c,binding,ctx,split,role,finish,labels,kind,?_,depth⟩
  change accessWord g access.val=accessWord g pre++(.body::accessWord g loop)
  rw [split,accessWord_append g pre loop nonempty]
  obtain ⟨tail,loopEq⟩ := List.head?_eq_some_iff.mp binding.start
  rw [loopEq]
  have token : arrivalWord g (.inl ⟨binding.binder,binding.body⟩)=[.body] :=
    lambda_body_word _ _ binding.isLam binding.body_role
  simp only [List.flatMap_cons,token,List.singleton_append,accessWord]
/-- A matched syntax variable supplies the actual original BindingSuffix;
its parent is the lambda occurrence in that literal prefix, not a chosen node. -/
theorem Matches.variable_binding_access {t : Term} (matching : Matches g root t)
    (access : RootAccess g root) {k : Nat}
    (lookup : subtermAt t (accessWord g access.val)=some (.var k)) :
    ∃ (parent : RootAccess g root) (loop : List (Endpoint g)) (a b c : Context)
      (binding : BindingLoop g loop b c) (ctx : Port (g.label binding.binder).sort) (body : Term),
      access.val=parent.val++loop ∧ HEq ctx (Sum.inl () : Port (.op .lam)) ∧
      parent.val.getLast?=some (g.wire (.inl ⟨binding.binder,ctx⟩)) ∧
      Labelling g parent.val a b ∧
      subtermAt t (accessWord g parent.val)=some (.lam body) ∧
      accessWord g access.val=accessWord g parent.val++(.body::accessWord g loop) ∧
      k=binderDepth (accessWord g loop) := by
  obtain ⟨bijection,corresponds,_⟩ := matching
  obtain ⟨word,u,atU,observes⟩ := corresponds access
  rw [←word] at atU
  have eq : u=.var k := Option.some.inj (atU.symm.trans lookup)
  subst u
  obtain ⟨parent,loop,a,b,c,binding,ctx,split,role,finish,labels,kind,words,depth⟩ :=
    access.binding_prefix observes.2.1
  obtain ⟨parentWord,subterm,atParent,parentObserves⟩ := corresponds parent
  have shape : (syntaxShape subterm).kind=.lam := Option.some.inj (parentObserves.1.symm.trans kind)
  cases subterm with
  | var j => cases shape
  | app fn arg => cases shape
  | lam body =>
    refine ⟨parent,loop,a,b,c,binding,ctx,body,split,role,finish,labels,?_,words,depth⟩
    simpa only [parentWord] using atParent
end
end Lamping.AG

