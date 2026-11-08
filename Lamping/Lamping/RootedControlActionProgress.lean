import Lamping.Lamping.WholeVisitActionWordTransport
import Lamping.Lamping.SourceActionKeptAccess
import Lamping.Lamping.ActionMatching
import Lamping.Lamping.RedexOccurrenceFragments

namespace Lamping.AG
open Graph Lambda ExposureScheduling

/-- Two occurrences emitting the final token of one literal list determine
exactly the same suffix. Empty emitted tails, not endpoint-value injectivity,
exclude different cuts. Repeated physical values are allowed. -/
private theorem last_token_suffix_unique {A S : Type} (emit : A → List S) (symbol : S)
    (before otherBefore : List A) (item otherItem : A) (after otherAfter : List A)
    (same : before++item::after=otherBefore++otherItem::otherAfter)
    (itemToken : emit item=[symbol]) (otherToken : emit otherItem=[symbol])
    (afterZero : after.flatMap emit=[]) (otherZero : otherAfter.flatMap emit=[]) :
    item::after=otherItem::otherAfter := by
  induction before generalizing otherBefore with
  | nil =>
    cases otherBefore with
    | nil => exact same
    | cons x xs =>
      have rest := (List.cons.inj same).2
      rw [rest] at afterZero
      change (xs++otherItem::otherAfter).flatMap emit=[] at afterZero
      rw [List.flatMap_append,List.flatMap_cons,otherToken,otherZero] at afterZero
      have impossible := (List.append_eq_nil_iff.mp afterZero).2
      cases impossible
  | cons x xs ih =>
    cases otherBefore with
    | nil =>
      have rest := (List.cons.inj same).2
      rw [←rest] at otherZero
      change (xs++item::after).flatMap emit=[] at otherZero
      rw [List.flatMap_append,List.flatMap_cons,itemToken,afterZero] at otherZero
      have impossible := (List.append_eq_nil_iff.mp otherZero).2
      cases impossible
    | cons y ys =>
      have parts := List.cons.inj same
      exact ih ys parts.2

section Words
variable {N B W : Type} [FiniteNames N] [FiniteNames B] [FiniteNames W]
variable (g : Net signature N B W)
private theorem overlap_word (before : List (Endpoint g)) (nonempty : before≠[])
    (pivot : Endpoint g) (tail : List (Endpoint g)) :
    accessWord g (before++pivot::tail)=
      accessWord g (before++[pivot])++accessWord g (pivot::tail) := by
  cases before with
  | nil => exact False.elim (nonempty rfl)
  | cons e before =>
    simp only [List.cons_append,accessWord,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc]
private theorem app_function_token (actual : Graph.Label signature)
    (port : Port actual.sort) (i : Nat) (labelEq : actual=label .app i)
    (role : HEq port (Sum.inl () : Port (.op .app))) :
    (match actual.sort,port with
      | .op .app,.inl () => [.fn]
      | .op .app,.inr true => [.arg]
      | .op .lam,.inr true => [.body]
      | _,_ => ([] : Path))=[.fn] := by
  subst actual
  have same : port=Sum.inl () := eq_of_heq role
  subst port
  rfl
private theorem connection_function_token (connection : RedexConnection g)
    {head : Endpoint g} (starts : connection.edges.head?=some head) :
    arrivalWord g head=[.fn] := by
  have same : head=.inl ⟨connection.app,connection.appPort⟩ :=
    Option.some.inj (starts.symm.trans connection.start)
  subst head
  exact app_function_token _ connection.appPort connection.appIndex
    connection.appLabel connection.appPrincipal
end Words

private theorem control_auxiliary_arrival_empty (actual : Graph.Label signature)
    (port : Port actual.sort) (op : Op) (i : Nat)
    (labelEq : actual=label op i) (control : op=.fan ∨op=.cro ∨op=.bra) :
    (match actual.sort,port with
      | .op .app,.inl () => ([.fn] : Path)
      | .op .app,.inr true => [.arg]
      | .op .lam,.inr true => [.body]
      | _,_ => [])=[] := by
  subst actual
  rcases control with rfl |rfl |rfl <;> cases port <;> rfl

private theorem control_auxiliary_kind_none (op : Op) (p : Aux op)
    (control : op=.fan ∨op=.cro ∨op=.bra) :
    portKind (.op op) (.inr p)=none := by
  rcases control with rfl |rfl |rfl <;> rfl

section
variable {s : Schema} {K B W V : Type}
variable [FiniteNames K] [FiniteNames B] [FiniteNames W] [FiniteNames V]
variable {kept : K → Graph.Label signature}
variable (site : PathSite s kept (B:=B) (W:=W) (V:=V))
local notation "cut" => cutFragment site.net (pathPartition s V) site.closed

private theorem active_control_of_action (action : IsAction s) :
    s.active=.fan ∨s.active=.cro ∨s.active=.bra := by
  cases action with
  | fan => exact Or.inl rfl
  | cro => exact Or.inr (Or.inl rfl)
  | bra => exact Or.inr (Or.inr rfl)

/-- Unlike arbitrary proper passive operators, both removed controls emit no
syntax token at any auxiliary frontier. This equality uses actual constructors. -/
private theorem outside_emission_control
    (activeControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (e : Endpoint cut) : arrivalWord site.net (site.outsideEnd e)=arrivalWord cut e := by
  rcases e with ⟨node,p⟩|((boundary|frontier)|⟨vertex,direction⟩)
  · rfl
  · rfl
  · cases frontier with
    | inl p =>
      exact control_auxiliary_arrival_empty (label s.active s.low) (.inr p)
        s.active s.low rfl activeControl
    | inr p =>
      exact control_auxiliary_arrival_empty (label s.passive s.high) (.inr p)
        s.passive s.high rfl passiveControl
  · rfl

private theorem outside_kind_control
    (activeControl : s.active=.fan ∨s.active=.cro ∨s.active=.bra)
    (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    (e : Endpoint cut) :
    accessKind site.reduce [AG.plugLeft cut s.right.net e]=
      accessKind site.net [site.outsideEnd e] := by
  change accessKind (plug cut s.right.net) [AG.plugLeft cut s.right.net e] =
    accessKind site.net [site.outsideEnd e]
  simp only [accessKind,List.getLast?_singleton,Option.bind_some]
  rw [plugLeft_wire,site.outsideEnd_wire]
  generalize (cut).wire e=terminal
  rcases terminal with ⟨node,p⟩|((boundary|frontier)|⟨vertex,direction⟩)
  · rfl
  · rfl
  · cases frontier with
    | inl p => exact (control_auxiliary_kind_none s.active p activeControl).symm
    | inr p => exact (control_auxiliary_kind_none s.passive p passiveControl).symm
  · rfl

private theorem physical_control_word_raw_root (raw : List (PlugSegment cut s.right.net)) :
    controlWord site.reduce (raw.map (plugEnd (cut).label s.right.net.label))=
      actionRawControlWord site raw := by
  cases raw with
  | nil => rfl
  | cons e tail =>
    change (tail.map (plugEnd (cut).label s.right.net.label)).flatMap
      (departureWord site.reduce)=tail.flatMap (Sum.elim (departureWord cut) (departureWord s.right.net))
    rw [List.flatMap_map]
    apply congrArg (fun f => tail.flatMap f)
    funext piece
    rcases piece with (⟨node,p⟩|((boundary|frontier)|⟨vertex,direction⟩))|
      (⟨node,p⟩|(frontier|⟨vertex,direction⟩)) <;> rfl

/-- A constructed physical RHS is attached to THIS original root child and
its final function-token cut. Target Matches and the target access are derived;
its complete connection is proved equal to the transported list before any
progress conclusion is used. Source outside endpoints and selected principal
membership are physical facts, not a wanted target/word/rank certificate. -/
theorem ActualRedexAccess.internal_action_word_progress
    (action : IsAction s) (passiveControl : s.passive=.fan ∨s.passive=.cro ∨s.passive=.bra)
    {root : B} {current : Lambda.Labelled.LTerm} {redex : RedexOcc current.erase}
    (source : ActualRedexAccess site.net root redex)
    {rootInput output : Context}
    (sourceAssignment : Labelling site.net source.child.val rootInput output)
    {directions : B → Bool} {depths : B → Int}
    (matching : Matches site.net root current.erase) (inputs : RootInputs site.net root)
    (flow : FlowBalance site.net directions) (positive : directions root=true)
    (balance : IndexedLevelBalance site.net depths) (rootDepth : depths root=0)
    (oldT : Transparency site.net root) (principal : SiteActionPrincipal site)
    (first last : Endpoint cut)
    (sourceHead : source.connection.edges.head?=some (site.outsideEnd first))
    (sourceEnd : source.connection.edges.getLast?=some (site.outsideEnd last))
    (selected : (.inl ⟨.inr (.inl ()),.inl ()⟩ : Endpoint site.net)∈source.connection.edges) :
    ∃ target : ActualRedexAccess site.reduce root redex,
      Labelling site.reduce target.child.val rootInput output ∧
      ∃ seam,Labelling site.net source.connection.edges seam output ∧
      Labelling site.reduce target.connection.edges seam output ∧
      ActionCanonicalBlocks site principal
        (target.connection.edges.map (plugEnd (cut).label s.right.net.label).invFun)
        source.connection.edges ∧
      (controlWord site.reduce target.connection.edges).length=
        (controlWord site.net source.connection.edges).length ∧
      inversions (controlWord site.reduce target.connection.edges)<
        inversions (controlWord site.net source.connection.edges) := by
  have activeControl := active_control_of_action action
  obtain ⟨n,visits⟩ := source.whole_control_visits site activeControl passiveControl principal
  have visitPositive := visits.positive_of_principal_occurs site selected
  obtain ⟨oldTail,pieceSplit⟩ := List.head?_eq_some_iff.mp sourceHead
  have oldChildLabels := sourceAssignment
  have oldChildSplit : source.child.val=source.parent.val++site.outsideEnd first::oldTail := by
    rw [source.split,pieceSplit]
  rw [oldChildSplit] at oldChildLabels
  obtain ⟨seam,oldRootPrefixLabels,oldPieceLabels⟩ := oldChildLabels.split_segment
  have oldPiece : Labelling site.net source.connection.edges seam output := by
    rw [pieceSplit]
    exact oldPieceLabels
  obtain ⟨raw,path,canonical,rawHead,rawLast,exchange⟩ :=
    visits.action_word_expansion site action passiveControl oldPiece first last sourceHead sourceEnd
  let targetPiece : List (Endpoint site.reduce) := raw.map (plugEnd (cut).label s.right.net.label)
  let targetFirst : Endpoint site.reduce := AG.plugLeft cut s.right.net first
  have pieceLabels : Labelling site.reduce targetPiece seam output :=
    (path.labelling cut s.right.net).actual cut s.right.net
  have pieceHead : targetPiece.head?=some (targetFirst) := by
    rw [List.head?_map,rawHead]
    rfl
  have pieceEnd : targetPiece.getLast?=some (AG.plugLeft cut s.right.net last) := by
    rw [List.getLast?_map,rawLast]
    rfl
  have pieceWord : accessWord site.reduce targetPiece=[] :=
    (canonical.word site path).trans source.connection.emptyWord
  have physicalExchange : ParallelControlExchanges
      (controlWord site.reduce targetPiece) (controlWord site.net source.connection.edges) n := by
    have physicalWord := physical_control_word_raw_root site raw
    rw [physicalWord]
    exact exchange
  have parentNonempty : source.parent.val≠[] := by
    intro empty
    have rooted := source.parent.property.2.1
    rw [empty] at rooted
    cases rooted
  have oldRooted : (source.parent.val++[site.outsideEnd first]).head?=some (.inr (.inl root)) := by
    rw [List.head?_append,source.parent.property.2.1]
    rfl
  obtain ⟨targetPrefix,prefixLabels,prefixHead,prefixEnd,prefixWord⟩ :=
    site.action_source_outside_word action matching inputs flow positive
      oldRootPrefixLabels oldRooted first (by simp)
  obtain ⟨targetBefore,prefixSplit⟩ := List.getLast?_eq_some_iff.mp prefixEnd
  change targetPrefix=targetBefore++[targetFirst] at prefixSplit
  obtain ⟨targetTail,targetPieceSplit⟩ := List.head?_eq_some_iff.mp pieceHead
  have targetPrefixLabels : Labelling site.reduce
      (targetBefore++[targetFirst]) rootInput seam := by
    rw [←prefixSplit]
    exact prefixLabels
  have targetPieceLabels : Labelling site.reduce
      (targetFirst::targetTail) seam output := by
    rw [←targetPieceSplit]
    exact pieceLabels
  let childList : List (Endpoint site.reduce) := targetBefore++targetFirst::targetTail
  have childLabels : Labelling site.reduce childList rootInput output :=
    targetPrefixLabels.join targetPieceLabels
  have childRooted : childList.head?=some (.inr (.inl root)) := by
    cases targetBefore with
    | nil => simpa only [prefixSplit,List.nil_append,List.head?_cons] using prefixHead
    | cons e es => simpa only [prefixSplit,List.cons_append,List.head?_cons] using prefixHead
  have sourceToken : arrivalWord site.net (site.outsideEnd first)=[.fn] :=
    connection_function_token site.net source.connection sourceHead
  have targetToken : arrivalWord site.reduce (targetFirst)=[.fn] := by
    change arrivalWord (plug cut s.right.net) (AG.plugLeft cut s.right.net first)=[.fn]
    rw [arrivalWord_plugLeft,←outside_emission_control site activeControl passiveControl]
    exact sourceToken
  have targetBeforeNonempty : targetBefore≠[] := by
    intro empty
    have atRoot : targetFirst=(.inr (.inl root) : Endpoint site.reduce) := by
      exact Option.some.inj (by
        simpa only [prefixSplit,empty,List.nil_append,List.head?_cons] using prefixHead)
    rw [atRoot] at targetToken
    cases targetToken
  have oldPrefixWord : accessWord site.net (source.parent.val++[site.outsideEnd first])=
      accessWord site.net source.child.val := by
    have word := overlap_word site.net source.parent.val parentNonempty (site.outsideEnd first) oldTail
    have zero : accessWord site.net (site.outsideEnd first::oldTail)=[] := by
      rw [←pieceSplit]
      exact source.connection.emptyWord
    rw [zero,List.append_nil,←oldChildSplit] at word
    exact word.symm
  have childWord : accessWord site.reduce childList=redex.val++[.fn] := by
    have word := overlap_word site.reduce targetBefore targetBeforeNonempty
      (targetFirst) targetTail
    have zeroTail : accessWord site.reduce (targetFirst::targetTail)=[] := by
      rw [←targetPieceSplit]
      exact pieceWord
    rw [zeroTail,List.append_nil,←prefixSplit,prefixWord,oldPrefixWord] at word
    exact word.trans source.childWord
  have childEnd : childList.getLast?=some (AG.plugLeft cut s.right.net last) := by
    have sameEnd : childList.getLast?=targetPiece.getLast? := by
      rw [targetPieceSplit]
      simp only [childList,List.getLast?_append,List.getLast?_cons,Option.some_or]
    exact sameEnd.trans pieceEnd
  have oldChildEnd : source.child.val.getLast?=some (site.outsideEnd last) := by
    rw [source.split,List.getLast?_append,sourceEnd]
    rfl
  have childKind : accessKind site.reduce childList=accessKind site.net source.child.val := by
    have kind := outside_kind_control site activeControl passiveControl last
    simpa only [accessKind,childEnd,oldChildEnd,List.getLast?_singleton,Option.bind_some] using kind
  obtain ⟨newFlow⟩ := site.reduce_flowBalance flow
  have childForward := childLabels.root_forward_of_flow newFlow root childRooted positive
  have childTyped : ∃ k,accessKind site.reduce childList=some k := by
    rw [childKind]
    exact source.child.property.2.2
  let constructedChild : RootAccess site.reduce root :=
    ⟨childList,⟨⟨⟨rootInput,output,childLabels⟩,childForward⟩,childRooted,childTyped⟩⟩
  have targetMatches := site.action_matches_rootInputs action flow root positive balance rootDepth inputs oldT matching
  obtain ⟨target⟩ := targetMatches.actual_redex_access redex
  have sameChild : constructedChild=target.child :=
    targetMatches.accessWord_injective (childWord.trans target.childWord.symm)
  have childLiteral : childList=target.child.val := congrArg Subtype.val sameChild
  obtain ⟨actualHead,actualHeadEq⟩ := List.head?_eq_some_iff.mp target.connection.start
  have actualHeadToken : arrivalWord site.reduce
      (.inl ⟨target.connection.app,target.connection.appPort⟩)=[.fn] :=
    connection_function_token site.reduce target.connection target.connection.start
  have sameLists : targetBefore++targetFirst::targetTail=
      target.parent.val++(.inl ⟨target.connection.app,target.connection.appPort⟩)::actualHead := by
    change childList=_
    rw [childLiteral,target.split,actualHeadEq]
  have zeroTransported : targetTail.flatMap (arrivalWord site.reduce)=[] := by
    simpa only [targetPieceSplit,accessWord] using pieceWord
  have zeroActual : actualHead.flatMap (arrivalWord site.reduce)=[] := by
    simpa only [actualHeadEq,accessWord] using target.connection.emptyWord
  have suffixSame := last_token_suffix_unique (arrivalWord site.reduce) Step.fn
    targetBefore target.parent.val (targetFirst)
    (.inl ⟨target.connection.app,target.connection.appPort⟩) targetTail actualHead
    sameLists targetToken actualHeadToken zeroTransported zeroActual
  have connectionEq : target.connection.edges=targetPiece := by
    rw [actualHeadEq,targetPieceSplit]
    exact suffixSame.symm
  have actualCanonical : ActionCanonicalBlocks site principal
      (target.connection.edges.map (plugEnd (cut).label s.right.net.label).invFun)
      source.connection.edges := by
    rw [connectionEq]
    simpa only [targetPiece,List.map_map,Function.comp_def,
      (plugEnd (cut).label s.right.net.label).left_inv,List.map_id_fun'] using canonical
  obtain ⟨length,strict⟩ := physicalExchange.strict_of_positive visitPositive
  have actualChildLabels : Labelling site.reduce target.child.val rootInput output := by
    rw [←childLiteral]
    exact childLabels
  have actualPieceLabels : Labelling site.reduce target.connection.edges seam output := by
    rw [connectionEq]
    exact pieceLabels
  exact ⟨target,actualChildLabels,seam,oldPiece,actualPieceLabels,actualCanonical,
    by simpa only [connectionEq] using length,by simpa only [connectionEq] using strict⟩
end
end Lamping.AG
