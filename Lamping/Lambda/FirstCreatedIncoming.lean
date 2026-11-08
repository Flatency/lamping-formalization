import Lamping.Lambda.FirstNewReadingOrigins
import Lamping.Lambda.PrerequisiteEdgeOrder
namespace Lamping.Lambda.Labelled
/-- Incoming positions actually created by THIS beta event, computed from
its literal site and the original bound-variable occurrences in its body. -/
def BetaCreatedIncoming (body : LTerm) (site edge : Path) : Prop :=
  edge=site ∨(edge=site++edge.drop site.length ∧
    ArgumentOccurrence body.erase (edge.drop site.length))
instance (body : LTerm) (site edge : Path) : Decidable (BetaCreatedIncoming body site edge) := by
  unfold BetaCreatedIncoming ArgumentOccurrence
  infer_instance

theorem betaCreatedIncoming_iff : BetaCreatedIncoming body site edge ↔
    edge=site ∨∃ q,ArgumentOccurrence body.erase q ∧edge=site++q := by
  constructor
  · rintro (result | ⟨equal,occurs⟩)
    · exact Or.inl result
    · exact Or.inr ⟨_,occurs,equal⟩
  · rintro (result | ⟨q,occurs,equal⟩)
    · exact Or.inl result
    · right
      rw [equal,List.drop_left]
      exact ⟨rfl,occurs⟩

/-- The finite cut data are computed, with no semantic or proof choice. -/
def firstCreatedCut (body : LTerm) (site : Path) : List Path →Option (List Path ×Path ×List Path)
  | [] => none
  | edge::rest =>
    if BetaCreatedIncoming body site edge then some ([],edge,rest)
    else match firstCreatedCut body site rest with
      | none => none
      | some (before,selected,after) => some (edge::before,selected,after)

theorem firstCreatedCut_sound
    (computed : firstCreatedCut body site edges=some (before,edge,after)) :
    edges=before++(edge::after) ∧BetaCreatedIncoming body site edge ∧
      ∀ old∈before,¬BetaCreatedIncoming body site old := by
  induction edges generalizing before edge after with
  | nil => cases computed
  | cons head tail ih =>
    by_cases created : BetaCreatedIncoming body site head
    · simp only [firstCreatedCut,if_pos created] at computed
      cases Option.some.inj computed
      exact ⟨rfl,created,by intro old member; cases member⟩
    · cases tailCut : firstCreatedCut body site tail with
      | none => simp only [firstCreatedCut,if_neg created,tailCut] at computed; cases computed
      | some cut =>
        obtain ⟨oldBefore,selected,oldAfter⟩ := cut
        simp only [firstCreatedCut,if_neg created,tailCut] at computed
        cases Option.some.inj computed
        obtain ⟨equal,selectedCreated,unread⟩ := ih tailCut
        refine ⟨by rw [equal]; rfl,selectedCreated,?_⟩
        intro old member
        rcases List.mem_cons.mp member with equal | below
        · subst old; exact created
        · exact unread old below

theorem firstCreatedCut_exists
    (member : edge∈edges) (created : BetaCreatedIncoming body site edge) :
    ∃ before selected after,firstCreatedCut body site edges=some (before,selected,after) := by
  induction edges with
  | nil => cases member
  | cons head tail ih =>
    by_cases headCreated : BetaCreatedIncoming body site head
    · exact ⟨[],head,tail,by simp only [firstCreatedCut,if_pos headCreated]⟩
    · have below : edge∈tail := by
        rcases List.mem_cons.mp member with equal | below
        · exact False.elim (headCreated (equal ▸ created))
        · exact below
      obtain ⟨before,selected,after,computed⟩ := ih below
      exact ⟨head::before,selected,after,by simp only [firstCreatedCut,if_neg headCreated,computed]⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
private theorem split_unique (nodup : edges.Nodup)
    (left : edges=before++(edge::after)) (right : edges=otherBefore++(edge::otherAfter)) :
    before=otherBefore ∧after=otherAfter := by
  have noLeft : edge∉before := by
    intro member
    have nd := nodup
    rw [left] at nd
    exact (List.nodup_append.mp nd).2.2 edge member edge List.mem_cons_self rfl
  have noRight : edge∉otherBefore := by
    intro member
    have nd := nodup
    rw [right] at nd
    exact (List.nodup_append.mp nd).2.2 edge member edge List.mem_cons_self rfl
  rcases List.append_eq_append_iff.mp (left.symm.trans right) with ⟨extra,prefixEq,tailEq⟩ |
      ⟨extra,prefixEq,tailEq⟩
  · cases extra with
    | nil => exact ⟨by simpa only [List.append_nil] using prefixEq.symm,
        (List.cons.inj (by simpa only [List.nil_append] using tailEq)).2⟩
    | cons head rest =>
      apply False.elim
      apply noRight
      rw [prefixEq]
      apply List.mem_append_right
      exact List.mem_cons.mpr (Or.inl (List.cons.inj tailEq).1)
  · cases extra with
    | nil => exact ⟨by simpa only [List.append_nil] using prefixEq,
        (List.cons.inj (by simpa only [List.nil_append] using tailEq)).2.symm⟩
    | cons head rest =>
      apply False.elim
      apply noLeft
      rw [prefixEq]
      apply List.mem_append_right
      exact List.mem_cons.mpr (Or.inl (List.cons.inj tailEq).1)

/-- The computed cut is synchronized with the supplied actual chain, not
with a separately guessed finite prefix or ordinal. -/
theorem PrerequisiteChain.first_created_cut
    (chain : PrerequisiteChain t start edges)
    (hasCreated : ∃ edge∈edges,BetaCreatedIncoming body site edge) :
    ∃ before edge after middle,firstCreatedCut body site edges=some (before,edge,after) ∧
      edges=before++(edge::after) ∧PrerequisitePrefix t start before middle ∧
      PrerequisiteChain t middle (edge::after) ∧PrerequisiteReads t middle edge ∧
      BetaCreatedIncoming body site edge ∧∀ old∈before,¬BetaCreatedIncoming body site old := by
  obtain ⟨someEdge,member,created⟩ := hasCreated
  obtain ⟨before,edge,after,computed⟩ := firstCreatedCut_exists member created
  obtain ⟨equal,selected,unread⟩ := firstCreatedCut_sound computed
  have edgeMember : edge∈edges := by rw [equal]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨oldBefore,oldAfter,middle,oldEqual,segment,remainder,reads⟩ := chain.split_at_member edgeMember
  obtain ⟨beforeEq,afterEq⟩ := split_unique chain.nodup equal oldEqual
  subst oldBefore
  subst oldAfter
  exact ⟨before,edge,after,middle,computed,equal,segment,remainder,reads,selected,unread⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Labelled
/-- All actual result/copy heads in BEFORE are excluded by the computed
first-created predicate, including the result/copy overlap. -/
theorem first_created_unread_heads
    {body : LTerm} {site : Path} {before : List Path}
    (unread : ∀ old∈before,¬BetaCreatedIncoming body site old) :
    site∉before ∧∀ q,ArgumentOccurrence body.erase q →site++q∉before := by
  refine ⟨?_,?_⟩
  · intro member
    exact unread site member (Or.inl rfl)
  · intro q occurs member
    exact unread _ member (betaCreatedIncoming_iff.mpr (Or.inr ⟨q,occurs,rfl⟩))

/-- The real first-created RESULT split supplies the universal BEFORE
restriction used by the result-prefix theorem; no caller unread certificate. -/
theorem PrerequisiteChain.first_created_result_before
    (chain : PrerequisiteChain t start edges)
    (computed : firstCreatedCut body site edges=some (before,site,after)) :
    ∀ otherBefore otherAfter,edges=otherBefore++(site::otherAfter) →
      ∀ q,ArgumentOccurrence body.erase q →site++q∉otherBefore := by
  obtain ⟨equal,created,unread⟩ := firstCreatedCut_sound computed
  intro otherBefore otherAfter otherEqual
  obtain ⟨beforeEq,afterEq⟩ := split_unique chain.nodup equal otherEqual
  subst otherBefore
  exact (first_created_unread_heads unread).2

/-- Computation selects the literal first-created edge. The actual chain
constructs its SAME prefix/reader, then the actual beta classifies its old
neighbors. No new-edge guess from repeated label values is made. -/
theorem StepAt.first_created_reading_origins
    {source target body argument : LTerm} {site start : Path} {beta alpha : Label}
    (step : StepAt site source target)
    (redex : source.subterm site=some (.app beta (.lam alpha body) argument))
    (chain : PrerequisiteChain target start edges)
    (hasCreated : ∃ edge∈edges,BetaCreatedIncoming body site edge) :
    ∃ before edge after middle oldStart first last,
      firstCreatedCut body site edges=some (before,edge,after) ∧
      edges=before++(edge::after) ∧PrerequisitePrefix target start before middle ∧
      PrerequisiteChain target middle (edge::after) ∧PrerequisiteReads target middle edge ∧
      BetaIncomingReadingOrigin body argument site edge middle oldStart first last ∧
      PrerequisiteChain source oldStart [first,site++[.fn]] ∧
      (∃ oldLast,source.subterm last=some oldLast) ∧
      BetaCreatedIncoming body site edge ∧∀ old∈before,¬BetaCreatedIncoming body site old := by
  obtain ⟨before,edge,after,middle,computed,equal,segment,remainder,reads,created,unread⟩ :=
    chain.first_created_cut hasCreated
  obtain ⟨oldStart,first,last,origin⟩ :=
    step.created_reading_origin redex reads (betaCreatedIncoming_iff.mp created)
  obtain ⟨oldChain,oldLast⟩ := origin.old_prerequisite redex
  exact ⟨before,edge,after,middle,oldStart,first,last,computed,equal,segment,remainder,reads,
    origin,oldChain,oldLast,created,unread⟩
end Lamping.Lambda.Labelled

namespace Lamping.Lambda.Labelled
/-- Two literal cuts at the same member of THIS actual chain coincide. -/
theorem PrerequisiteChain.first_created_split_unique
    (chain : PrerequisiteChain t start edges)
    (left : edges=before++(edge::after)) (right : edges=otherBefore++(edge::otherAfter)) :
    before=otherBefore ∧after=otherAfter := split_unique chain.nodup left right
end Lamping.Lambda.Labelled