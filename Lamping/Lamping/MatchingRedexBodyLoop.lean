import Lamping.Lamping.MatchingSourceBinders
import Lamping.Lamping.MatchingRedexEndpointUniqueness
namespace Lamping.AG
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B} {t : Term} {redex : RedexOcc t}

/-- A leaf lexically bound by this redex's original lambda supplies a real
ordinary binding loop whose ROOT prefix is the SAME actual function-child
access. Path/depth uniqueness locks the binder occurrence before its physical
node is identified; neither a loop nor a common-prefix certificate is input. -/
theorem ActualRedexAccess.bound_body_loop
    (source : ActualRedexAccess g root redex) (matching : Matches g root t)
    {body argument : Term} (lookup : subtermAt t redex.val=some (.app (.lam body) argument))
    (p : Path) (variableLookup : subtermAt body p=some (.var (binderDepth p))) :
    ∃ (leaf : RootAccess g root) (loop : List (Endpoint g)) (a b c : Context)
      (binding : BindingLoop g loop b c),
      accessWord g leaf.val=(redex.val++[.fn])++(.body::p) ∧
      leaf.val=source.child.val++loop ∧binding.binder=source.connection.lam ∧
      accessWord g loop=p ∧Labelling g source.child.val a b := by
  let path := (redex.val++[.fn])++(.body::p)
  have atVariable : subtermAt t path=some (.var (binderDepth p)) := by
    simp only [path,subtermAt_append,lookup,subtermAt,Option.bind_some]
    exact variableLookup
  let position : Position t := ⟨path,by rw [atVariable]; rfl⟩
  obtain ⟨leaf,word,_⟩ := Matches.observation g matching position
  have actualVariable : subtermAt t (accessWord g leaf.val)=some (.var (binderDepth p)) := by
    rw [word]
    exact atVariable
  obtain ⟨parent,loop,a,b,c,binding,ctx,_body,split,_role,finish,labels,_lookup,words,depth⟩ :=
    matching.variable_binding_access leaf actualVariable
  have paths : accessWord g parent.val++(.body::accessWord g loop)=(redex.val++[.fn])++(.body::p) :=
    words.symm.trans word
  have occurrence := binding_prefix_depth_unique paths depth.symm
  have parentEq : parent=source.child := matching.accessWord_injective (occurrence.1.trans source.childWord.symm)
  have childFinish : source.child.val.getLast?=some (g.wire (.inl ⟨source.connection.lam,source.connection.lamPort⟩)) := by
    rw [source.split,List.getLast?_append,source.connection.finish]
    rfl
  rw [parentEq] at finish split labels
  have wires := Option.some.inj (finish.symm.trans childFinish)
  have endpoints := congrArg g.wire.mate wires
  simp only [Pairing.involutive] at endpoints
  have binderEq : binding.binder=source.connection.lam := congrArg Sigma.fst (Sum.inl.inj endpoints)
  exact ⟨leaf,loop,a,b,c,binding,word,split,binderEq,occurrence.2,labels⟩
end
end Lamping.AG

