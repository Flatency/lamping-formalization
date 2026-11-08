import Lamping.Lamping.ReadbackFramedPaths
import Lamping.Lamping.MatchingSourceEdges
import Lamping.Lamping.RootPathInputs

namespace Lamping.AG.Readback
open Graph Lambda
section
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable {g : Net signature N B W} {root : B}

theorem RootAccess.terminal_arrival (access : RootAccess g root) :
    ∃ (last : Endpoint g) (arrival : NodePort signature N g.label) (kind : AccessKind),
      access.val.getLast?=some last ∧g.wire last=.inl arrival ∧
        portKind (g.label arrival.1).sort arrival.2=some kind := by
  obtain ⟨kind,kindEq⟩ := access.property.2.2
  unfold accessKind at kindEq
  cases lastEq : access.val.getLast? with
  | none => simp [lastEq] at kindEq
  | some last =>
    simp only [lastEq,Option.bind_some] at kindEq
    cases wireEq : g.wire last with
    | inl arrival => exact ⟨last,arrival,kind,rfl,wireEq,by simpa only [wireEq] using kindEq⟩
    | inr target => cases target <;> simp [wireEq] at kindEq

private def departureToken (kind : Kind) (port : Port kind) : Path :=
  match kind,port with
  | .op .app,.inl () => [.fn]
  | .op .app,.inr true => [.arg]
  | .op .lam,.inr true => [.body]
  | _,_ => []

private theorem child_token {kind : Kind} {ctx departure : Port kind} {step : Step}
    (roles : SyntaxChildPorts kind ctx departure step) :
    departureToken kind departure=[step] := by cases roles <;> rfl

/-- Following a fixed finite control suffix preserves the actual frame trace.
Every intermediate context is the output of the executable control step. -/
theorem FramedPath.follow_control_path {es : List (Endpoint g)} {before after : Context}
    (labels : Labelling g es before after)
    (controls : ∀ e f,(e,f)∈es.zip es.tail →ControlOnlyTurn (g:=g) e f)
    (first : Endpoint g) (headEq : es.head?=some first)
    (pre : List (Endpoint g)) (input data : ContextData) (frames : List (BinderFrame g))
    (trace : FramedPath g root input (pre++[first]) data frames)
    (dataEq : Context.ofList data=before) :
    ∃ output last,Context.ofList output=after ∧es.getLast?=some last ∧
      FramedPath g root input (pre++es) output frames ∧
        scanFuel g es.length first data=scanFuel g 1 last output := by
  induction labels generalizing first pre data with
  | single e before =>
    have same : e=first := by simpa using headEq
    subst first
    exact ⟨data,e,dataEq,rfl,trace,rfl⟩
  | @cons e f es before middle after turn tail ih =>
    have same : e=first := by simpa using headEq
    subst first
    have thisControl : ControlOnlyTurn (g:=g) e f := controls e f (by simp)
    obtain ⟨middleData,step,middleEq⟩ := scanOne_next_complete turn thisControl data dataEq
    have nextTrace : FramedPath g root input ((pre++[e])++[f]) middleData frames :=
      .scan trace (by simp) step
    have tailControls : ∀ x y,(x,y)∈(f::es).zip (f::es).tail →ControlOnlyTurn (g:=g) x y := by
      intro x y member
      apply controls x y
      simp only [List.tail_cons,List.zip_cons_cons]
      exact List.mem_cons.mpr (Or.inr member)
    obtain ⟨output,last,outputEq,lastEq,result,run⟩ := ih tailControls f rfl
      (pre++[e]) middleData nextTrace middleEq
    exact ⟨output,last,outputEq,by simpa only [List.getLast?_cons_cons] using lastEq,
      by simpa only [List.append_assoc,List.singleton_append] using result,
      by simpa only [List.length_cons,scanFuel,step] using run⟩

theorem FramedPath.follow_empty_word {es : List (Endpoint g)} {before after : Context}
    (labels : Labelling g es before after) (forward : Forward g es) (word : accessWord g es=[])
    (first : Endpoint g) (headEq : es.head?=some first)
    (pre : List (Endpoint g)) (input data : ContextData) (frames : List (BinderFrame g))
    (trace : FramedPath g root input (pre++[first]) data frames)
    (dataEq : Context.ofList data=before) :
    ∃ output last,Context.ofList output=after ∧es.getLast?=some last ∧
      FramedPath g root input (pre++es) output frames ∧
        scanFuel g es.length first data=scanFuel g 1 last output :=
  FramedPath.follow_control_path labels (forward.empty_word_control_only word)
    first headEq pre input data frames trace dataEq

/-- The root observation with zero syntax word is scanned from the actual
root and supplied finite input. The resulting frame trace and scanner output
share exactly one computed finite context. -/
theorem RootAccess.scan_root (access : RootAccess g root) (inputs : RootInputs g root)
    (word : accessWord g access.val=[]) (input : ContextData) :
    ∃ (arrival : NodePort signature N g.label) (kind : AccessKind) (data : ContextData),
      scanFuel g access.val.length (.inr (.inl root)) input=
        .stopped (.terminal arrival kind data) ∧
      FramedPath g root input access.val data [] ∧
      Labelling g access.val (Context.ofList input) (Context.ofList data) ∧
      access.val.getLast?=some (g.wire (.inl arrival)) ∧
      portKind (g.label arrival.1).sort arrival.2=some kind := by
  obtain ⟨output,labels⟩ := inputs.access access (Context.ofList input)
  have start : FramedPath g root input ([]++[.inr (.inl root)]) input [] := .initial
  obtain ⟨data,last,outputEq,lastEq,trace,run⟩ := FramedPath.follow_empty_word labels
    access.property.1.2 word (.inr (.inl root)) access.property.2.1 [] input input [] start rfl
  obtain ⟨actualLast,arrival,kind,actualLastEq,finish,terminal⟩ := RootAccess.terminal_arrival access
  have sameLast : last=actualLast := Option.some.inj (lastEq.symm.trans actualLastEq)
  subst actualLast
  have back : last=g.wire (.inl arrival) := by
    have same := congrArg g.wire.mate finish
    simpa only [Pairing.involutive] using same
  refine ⟨arrival,kind,data,?_,?_,?_,actualLastEq.trans (congrArg some back),terminal⟩
  · simpa only [scanFuel,scanOne,finish,terminal] using run
  · simpa only [List.nil_append] using trace
  · rw [outputEq]
    exact labels

/-- An existing matching child supplies one fixed finite zero-word scanner
suffix under the same root assignment as the current parent. The result data
is produced by scanning that very suffix; no new path is chosen mid-scan. -/
theorem Matches.scan_child {term : Term} (matching : Matches g root term)
    (inputs : RootInputs g root) (parent child : RootAccess g root) (step : Step)
    (word : accessWord g child.val=accessWord g parent.val++[step])
    (input : Context) (context : ContextData)
    (parentLabels : Labelling g parent.val input (Context.ofList context)) :
    ∃ (node : N) (ctx departure : Port (g.label node).sort)
      (tail : List (Endpoint g)) (arrival : NodePort signature N g.label)
      (kind : AccessKind) (data : ContextData),
      SyntaxChildPorts (g.label node).sort ctx departure step ∧
      parent.val.getLast?=some (g.wire (.inl ⟨node,ctx⟩)) ∧
      child.val=parent.val++(.inl ⟨node,departure⟩)::tail ∧
      scanFuel g (tail.length+1) (.inl ⟨node,departure⟩) context=
        .stopped (.terminal arrival kind data) ∧
      Labelling g child.val input (Context.ofList data) ∧
      child.val.getLast?=some (g.wire (.inl arrival)) ∧
      portKind (g.label arrival.1).sort arrival.2=some kind := by
  obtain ⟨node,ctx,departure,tail,roles,parentEnd,split,forward,splitLabels⟩ :=
    matching.syntax_child_fragment parent child step word
  obtain ⟨output,childLabels⟩ := inputs.access child input
  obtain ⟨middle,prefixLabels,suffixLabels⟩ := splitLabels input output childLabels
  have middleEq : middle=Context.ofList context := prefixLabels.output_unique parentLabels
  rw [middleEq] at suffixLabels
  have token : arrivalWord g (.inl ⟨node,departure⟩)=[step] := child_token roles
  have zero : accessWord g ((.inl ⟨node,departure⟩)::tail)=[] := by
    have same := word
    rw [split,accessWord_append g parent.val _ parentLabels.nonempty] at same
    simp only [List.flatMap_cons,token,List.singleton_append] at same
    have rest := List.append_cancel_left same
    exact (List.cons.inj rest).2
  obtain ⟨last,arrival,kind,lastEq,finish,terminal⟩ := RootAccess.terminal_arrival child
  have suffixLast : ((.inl ⟨node,departure⟩)::tail).getLast?=some last := by
    simpa only [split,List.getLast?_append,List.getLast?_cons,Option.some_or] using lastEq
  obtain ⟨first,data,headEq,outputEq,run⟩ := scanFuel_of_empty_word suffixLabels forward zero
    last suffixLast arrival kind finish terminal context rfl
  have firstEq : first=(.inl ⟨node,departure⟩ : Endpoint g) := by simpa using headEq.symm
  subst first
  refine ⟨node,ctx,departure,tail,arrival,kind,data,roles,parentEnd,split,?_,?_,?_,terminal⟩
  · simpa only [List.length_cons] using run
  · rw [outputEq]
    exact childLabels
  · rw [lastEq]
    have back := congrArg g.wire.mate finish
    exact congrArg some (by simpa only [Pairing.involutive] using back)

end
end Lamping.AG.Readback
