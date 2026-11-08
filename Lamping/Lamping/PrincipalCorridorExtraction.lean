import Lamping.Lamping.FirstNodeDecomposition
import Lamping.Lamping.TransparentCorridors
namespace Lamping.AG
open Graph

private theorem control_principal_side {i : Nat} {kind : Kind} {p q : Port kind} {a b : Context}
    (op : Op) (sort : kind=.op op) (control : op=.fan ∨op=.cro ∨op=.bra)
    (rule : Traversal i kind p q a b) :
    HEq p (Sum.inl () : Port (.op op)) ∨HEq q (Sum.inl () : Port (.op op)) := by
  cases rule with
  | direct rule => cases rule <;> cases op <;> simp_all [fanO,fanStar]
  | inverse rule => cases rule <;> cases op <;> simp_all [fanO,fanStar]

private theorem adjacent_append_right {A : Type} (pre suffix : List A) {e f : A}
    (pair : (e,f)∈suffix.zip suffix.tail) :
    (e,f)∈(pre++suffix).zip (pre++suffix).tail := by
  induction pre with
  | nil => exact pair
  | cons x pre ih =>
    cases shape : pre++suffix with
    | nil => simp [shape] at ih
    | cons y ys =>
      simpa only [List.cons_append,shape,List.tail_cons,List.zip_cons_cons] using
        List.mem_cons_of_mem (x,y) (by simpa only [shape] using ih)

private theorem selected_pair_mem {A : Type} (pre : List A) (e f : A) (tail : List A) :
    (e,f)∈(pre++e::f::tail).zip (pre++e::f::tail).tail :=
  adjacent_append_right pre (e::f::tail) (by simp)

section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W}

def IsPrincipal (port : NodePort signature N g.label) : Prop :=
  ∃ op,(g.label port.1).sort=.op op ∧HEq port.2 (Sum.inl () : Port (.op op))

/-- An actual node turn on a control-only path has a control label. -/
theorem FirstNodeTurn.control {es : List (Endpoint g)} {a b : Context}
    (piece : FirstNodeTurn (g:=g) es a b)
    (only : ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f) :
    ∃ op,(g.label piece.node).sort=.op op ∧(op=.fan ∨op=.cro ∨op=.bra) := by
  have pair : (piece.entry,piece.exit)∈es.zip es.tail := by
    simpa only [←piece.split] using selected_pair_mem piece.before piece.entry piece.exit piece.after
  rcases only _ _ pair with ⟨w,d,arrival,_⟩ |⟨node,p,q,op,sort,control,arrival,_⟩
  · rw [piece.arrives] at arrival
    cases arrival
  · have same : node=piece.node := congrArg Sigma.fst (Sum.inl.inj (arrival.symm.trans piece.arrives))
    subst node
    exact ⟨op,sort,control⟩

/-- A supplied finite control/W path between principal ports contains an
actual principal-to-principal transparent corridor. Its occurrence list is a
literal contiguous part of the original path. This constructs no extension
and assumes neither a rewrite site nor the desired normal-form conclusion. -/
theorem Labelling.principal_corridor {es : List (Endpoint g)} {a b : Context}
    (labels : Labelling g es a b)
    (only : ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f)
    (first last : NodePort signature N g.label)
    (firstPrincipal : IsPrincipal (g:=g) first) (lastPrincipal : IsPrincipal (g:=g) last)
    (start : es.head?=some (.inl first)) (finish : es.getLast?=some (g.wire (.inl last))) :
    ∃ route : TransparentCorridor g,IsPrincipal (g:=g) route.first ∧
      IsPrincipal (g:=g) route.last ∧∃ before after,es=before++route.edges++after := by
  generalize sizeEq : es.length=size
  induction size using Nat.strongRecOn generalizing es a b first with
  | ind size ih =>
    rcases labels.first_node with transparent |existsPiece
    · exact ⟨⟨first,last,es,start,finish,transparent⟩,firstPrincipal,lastPrincipal,[],[],by simp⟩
    · obtain ⟨piece⟩ := existsPiece
      obtain ⟨op,sort,control⟩ := piece.control only
      rcases control_principal_side op sort control piece.rule with arrivalPrincipal |exitPrincipal
      · let route : TransparentCorridor g := {
          first := first,last := ⟨piece.node,piece.incoming⟩,edges := piece.before++[piece.entry],
          start := by
            have same : (piece.before++[piece.entry]).head?=es.head? := by
              exact (by cases piece.before <;> rfl : (piece.before++[piece.entry]).head?=(piece.before++piece.entry::piece.exit::piece.after).head?).trans (congrArg List.head? piece.split).symm
            exact same.trans start,
          finish := by simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or];
                       rw [←piece.arrives,Pairing.involutive],
          transparent := piece.transparent }
        refine ⟨route,firstPrincipal,⟨op,sort,arrivalPrincipal⟩,[],piece.exit::piece.after,?_⟩
        simpa only [route,List.nil_append,List.append_assoc,List.singleton_append] using piece.split
      · have suffixOnly : ∀ e f,(e,f)∈(piece.exit::piece.after).zip (piece.exit::piece.after).tail →
            ControlOnlyTurn (g:=g) e f := by
          intro e f pair
          apply only e f
          simpa only [List.append_assoc,List.singleton_append,←piece.split] using
            adjacent_append_right (piece.before++[piece.entry]) (piece.exit::piece.after) pair
        have smaller : (piece.exit::piece.after).length<size := by
          have count := congrArg List.length piece.split
          simp only [List.length_append,List.length_cons] at count
          rw [←sizeEq]
          simp only [List.length_cons]; omega
        have suffixFinish : (piece.exit::piece.after).getLast?=some (g.wire (.inl last)) := by
          have actualFinish := (congrArg List.getLast? piece.split).symm.trans finish
          rw [List.getLast?_append] at actualFinish
          simpa only [List.getLast?_cons,Option.some_or] using actualFinish
        obtain ⟨route,left,right,before,after,split⟩ := ih _ smaller piece.suffix suffixOnly
          ⟨piece.node,piece.outgoing⟩ ⟨op,sort,exitPrincipal⟩
          (by rw [piece.leaves]; rfl) suffixFinish rfl
        refine ⟨route,left,right,(piece.before++[piece.entry])++before,after,?_⟩
        apply piece.split.trans
        simpa only [List.append_assoc,List.singleton_append] using
          congrArg (fun xs => piece.before++piece.entry::xs) split

/-- A genuine syntax-redex connection supplies the path to the finite
extraction theorem. The resulting corridor may have control endpoints; no
claim that it already has a compatible rewrite schema is made here. -/
theorem RedexConnection.principal_corridor (connection : RedexConnection g) :
    ∃ route : TransparentCorridor g,IsPrincipal (g:=g) route.first ∧
      IsPrincipal (g:=g) route.last ∧∃ before after,connection.edges=before++route.edges++after := by
  obtain ⟨a,b,labels⟩ := connection.proper.1
  exact labels.principal_corridor connection.control_only
    ⟨connection.app,connection.appPort⟩ ⟨connection.lam,connection.lamPort⟩
    ⟨.app,congrArg Label.sort connection.appLabel,connection.appPrincipal⟩
    ⟨.lam,congrArg Label.sort connection.lamLabel,connection.lamPrincipal⟩
    connection.start connection.finish
end
end Lamping.AG
