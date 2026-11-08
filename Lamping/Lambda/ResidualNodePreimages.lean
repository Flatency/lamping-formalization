import Lamping.Lambda.BetaChainExistenceReflection
import Lamping.Lambda.RootResidualPaths
import Lamping.Lambda.TagProjection
namespace Lamping.Lambda.Labelled
private theorem BetaNodePreimage.prepend_step (child : Step)
    (origin : BetaNodePreimage body argument site p old) :
    BetaNodePreimage body argument (child::site) (child::p) (child::old) := by
  cases origin with
  | context outside => exact .context (by rintro ⟨r,equal⟩;exact outside ⟨r,(List.cons.inj equal).2⟩)
  | retained lookup nonselected => exact .retained lookup nonselected
  | copied occurs lookup => exact .copied occurs lookup
private theorem root_tag_preimage {mb ma : Marked} {lb la : LTerm} {tags : List Path}
    (validBody : Marked.Valid mb) (validArgument : Marked.Valid ma)
    (bodyErase : lb.erase=mb.erase) (argErase : la.erase=ma.erase)
    (member : p∈Marked.tracePositions name (Marked.contract mb ma)) :
    ∃ old,old∈Marked.tracePositions name (.app tags (.lam mb) ma) ∧
      BetaNodePreimage lb la [] p old := by
  rcases Marked.contract_trace_iff.mp member with old | ⟨q,r,occurs,split,inside⟩
  · obtain ⟨bare,atBare,redex⟩ := Marked.tracePositions_sound validBody old
    rw [←bodyErase,←LTerm.erase_subterm] at atBare
    obtain ⟨node,lookup,erased⟩ := Option.map_eq_some_iff.mp atBare
    have nonselected : ∀ stamp,node≠.var stamp (binderDepth p) := by
      intro stamp equal
      rw [←erased,equal] at redex
      cases redex
    refine ⟨[.fn,.body]++p,?_,?_⟩
    · simp only [Marked.tracePositions,List.mem_append,List.mem_map]
      exact Or.inr (Or.inl ⟨.body::p,⟨p,old,rfl⟩,rfl⟩)
    · simpa only [List.nil_append] using
        (BetaNodePreimage.retained (site:=[]) lookup nonselected)
  · obtain ⟨bare,atBare,_⟩ := Marked.tracePositions_sound validArgument inside
    rw [←argErase,←LTerm.erase_subterm] at atBare
    obtain ⟨node,lookup,_⟩ := Option.map_eq_some_iff.mp atBare
    have actualOccurs : ArgumentOccurrence lb.erase q := by rw [bodyErase];exact occurs
    refine ⟨.arg::r,?_,?_⟩
    · simp only [Marked.tracePositions,List.mem_append,List.mem_map]
      exact Or.inr (Or.inr ⟨r,inside,rfl⟩)
    · rw [split]
      exact BetaNodePreimage.copied actualOccurs lookup
private theorem root_trace_position {tags : List Path}
    (member : p∈(if name∈tags then [[]] else [])) : p=[] := by
  split at member <;> simp_all
private theorem passive_valid {m : Marked} (valid : Marked.Valid m) : Marked.Valid m.passive := by
  induction m with
  | var => trivial
  | lam b ih => exact ih valid
  | app tags f a hf ha =>
    refine ⟨hf valid.1,ha valid.2.1,?_⟩
    intro nonempty
    obtain ⟨b,equal⟩ := valid.2.2 nonempty
    subst f;exact ⟨b.passive,rfl⟩
  | red tags b a hb ha => exact ⟨hb valid.1,ha valid.2,fun _=>⟨b.passive,rfl⟩⟩
end Lamping.Lambda.Labelled
namespace Lamping.Lambda.Marked
open Labelled
private theorem passive_trace_preimage
    (reduction : ReductionAt site m n) (passive : m.passive=m) (valid : Valid m)
    (turn : Labelled.StepAt site source target) (erased : source.erase=m.erase)
    (member : p∈tracePositions name n) :
    ∃ old beta alpha body argument,old∈tracePositions name m ∧
      source.subterm site=some (.app beta (.lam alpha body) argument) ∧
      BetaNodePreimage body argument site p old := by
  induction reduction generalizing source target p with
  | appRoot tags b a =>
    cases turn with
    | root beta alpha lb la =>
      simp only [LTerm.erase,Marked.erase,Term.app.injEq,Term.lam.injEq] at erased
      obtain ⟨old,oldMember,origin⟩ := root_tag_preimage (mb:=b) (ma:=a) (lb:=lb) (la:=la) valid.1 valid.2.1 erased.1 erased.2 member
      exact ⟨old,beta,alpha,lb,la,oldMember,rfl,origin⟩
  | redRoot => cases passive
  | @lam site m n reduction ih =>
    cases turn with
    | body turn =>
      have childErase := Term.lam.inj erased
      simp only [tracePositions,List.mem_map] at member
      obtain ⟨q,inside,rfl⟩ := member
      obtain ⟨old,beta,alpha,body,argument,oldMember,redex,origin⟩ :=
        ih (Marked.lam.inj passive) valid turn childErase inside
      exact ⟨.body::old,beta,alpha,body,argument,List.mem_map.mpr ⟨old,oldMember,rfl⟩,
        redex,origin.prepend_step .body⟩
  | @appL site f g tags a reduction ih =>
    cases turn with
    | fn turn =>
      have components := Term.app.inj erased
      simp only [tracePositions,List.mem_append,List.mem_map] at member
      rcases member with root | ⟨q,inside,rfl⟩ | ⟨q,inside,rfl⟩
      · have equal := root_trace_position root
        subst p
        obtain ⟨beta,alpha,body,argument,redex,_⟩ := (Labelled.StepAt.fn turn).head_lookups
        exact ⟨[],beta,alpha,body,argument,List.mem_append_left _ root,redex,
          .context (by rintro ⟨r,equal⟩;cases equal)⟩
      · obtain ⟨old,beta,alpha,body,argument,oldMember,redex,origin⟩ :=
          ih (Marked.app.inj passive).2.1 valid.1 turn components.1 inside
        refine ⟨.fn::old,beta,alpha,body,argument,?_,redex,origin.prepend_step .fn⟩
        simp only [tracePositions,List.mem_append,List.mem_map]
        exact Or.inr (Or.inl ⟨old,oldMember,rfl⟩)
      · obtain ⟨beta,alpha,body,argument,redex,_⟩ := (Labelled.StepAt.fn turn).head_lookups
        refine ⟨.arg::q,beta,alpha,body,argument,?_,redex,?origin⟩
        · simp only [tracePositions,List.mem_append,List.mem_map]
          exact Or.inr (Or.inr ⟨q,inside,rfl⟩)
        case origin => exact .context (by rintro ⟨r,equal⟩;cases equal)
  | @appR site a b tags f reduction ih =>
    cases turn with
    | arg turn =>
      have components := Term.app.inj erased
      simp only [tracePositions,List.mem_append,List.mem_map] at member
      rcases member with root | ⟨q,inside,rfl⟩ | ⟨q,inside,rfl⟩
      · have equal := root_trace_position root
        subst p
        obtain ⟨beta,alpha,body,argument,redex,_⟩ := (Labelled.StepAt.arg turn).head_lookups
        exact ⟨[],beta,alpha,body,argument,List.mem_append_left _ root,redex,
          .context (by rintro ⟨r,equal⟩;cases equal)⟩
      · obtain ⟨beta,alpha,body,argument,redex,_⟩ := (Labelled.StepAt.arg turn).head_lookups
        refine ⟨.fn::q,beta,alpha,body,argument,?_,redex,?origin⟩
        · simp only [tracePositions,List.mem_append,List.mem_map]
          exact Or.inr (Or.inl ⟨q,inside,rfl⟩)
        case origin => exact .context (by rintro ⟨r,equal⟩;cases equal)
      · obtain ⟨old,beta,alpha,body,argument,oldMember,redex,origin⟩ :=
          ih (Marked.app.inj passive).2.2 valid.2.1 turn components.2 inside
        refine ⟨.arg::old,beta,alpha,body,argument,?_,redex,origin.prepend_step .arg⟩
        simp only [tracePositions,List.mem_append,List.mem_map]
        exact Or.inr (Or.inr ⟨old,oldMember,rfl⟩)
  | redL => cases passive
  | redR => cases passive
end Lamping.Lambda.Marked

namespace Lamping.Lambda.Marked
open Labelled
/-- Names are transported through the actual substitution, independently of
labels or equality of redex degrees. -/
theorem ReductionAt.trace_node_preimage
    (reduction : ReductionAt site m n) (valid : Valid m)
    (turn : Labelled.StepAt site source target) (erased : source.erase=m.erase)
    (member : p∈tracePositions name n) :
    ∃ old beta alpha body argument,old∈tracePositions name m ∧
      source.subterm site=some (.app beta (.lam alpha body) argument) ∧
      BetaNodePreimage body argument site p old := by
  have passiveMember : p∈tracePositions name n.passive := by rw [passive_trace];exact member
  obtain ⟨old,beta,alpha,body,argument,oldMember,redex,origin⟩ :=
    passive_trace_preimage reduction.passive (passive_idempotent m)
      (passive_valid valid) turn (erased.trans (passive_erase m).symm) passiveMember
  exact ⟨old,beta,alpha,body,argument,by simpa only [passive_trace] using oldMember,redex,origin⟩
/-- SAME actual labelled schedule records app-occurrence ancestry for every
P04 old name. No current reinitialisation or degree-only identification. -/
theorem History.trace_node_history_preimage
    (marked : History ps m n) (valid : Valid m)
    (labels : Labelled.History ps source target) (erased : source.erase=m.erase)
    (member : p∈tracePositions name n) :
    ∃ old,old∈tracePositions name m ∧BetaNodeHistoryPreimage labels p old := by
  induction marked generalizing source target p with
  | nil => cases labels;exact ⟨p,member,.nil _ _⟩
  | cons reduction tail ih =>
    cases labels with
    | cons turn remaining =>
      have beta := turn.betaAt
      rw [erased] at beta
      obtain ⟨actual,actualStep,actualErase⟩ := lift_general_betaAt beta
      have equal := reduction.deterministic actualStep
      subst actual
      obtain ⟨middlePosition,middleMember,tailTrace⟩ :=
        ih (reduction.valid valid) remaining actualErase.symm member
      obtain ⟨old,beta,alpha,body,argument,oldMember,redex,origin⟩ :=
        reduction.trace_node_preimage valid turn erased middleMember
      exact ⟨old,oldMember,.one (step:=turn) redex origin tailTrace⟩
/-- At the original mark, an old application name is its literal coordinate.
The final app's whole operational ancestry therefore ends at THIS name. -/
theorem History.initial_name_node_preimage
    (marked : History ps (mark F source.erase) n)
    (labels : Labelled.History ps source target) (member : p∈tracePositions name n) :
    (∃ beta alpha body argument,source.subterm name=some (.app beta (.lam alpha body) argument)) ∧
      BetaNodeHistoryPreimage labels p name := by
  obtain ⟨old,oldMember,trace⟩ := marked.trace_node_history_preimage (valid_mark F source.erase) labels (erase_mark F source.erase).symm member
  obtain ⟨same,redexMember⟩ := (trace_mark F source.erase name old).mp oldMember
  subst old
  have redex := (mem_redexPositions _ _).mp redexMember
  obtain ⟨alpha,degree⟩ := degreeAt_exists source ⟨name,redex⟩
  obtain ⟨beta,body,argument,lookup⟩ := LTerm.degreeAt_redex degree
  exact ⟨⟨beta,alpha,body,argument,lookup⟩,trace⟩
/-- A selected residual's original F name is recovered at app-occurrence
level, not from equality of degrees or a physical lambda. -/
theorem RelativeOldHistory.selected_node_preimage
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (labels : Labelled.History ps source target)
    (member : p∈setResidualPositions F n) :
    ∃ name∈F,
      (∃ beta alpha body argument,source.subterm name=some (.app beta (.lam alpha body) argument)) ∧
      BetaNodeHistoryPreimage labels p name := by
  obtain ⟨name,chosen,residual⟩ := (mem_setResidualPositions F n p).mp member
  have general := ((relativeOld_iff_relative (selected_mark F source.erase)).mp old).general
  obtain ⟨redex,trace⟩ := general.initial_name_node_preimage labels residual
  exact ⟨name,chosen,redex,trace⟩
theorem RelativeOldHistory.selected_preimage_mem
    (old : RelativeOldHistory F ps (mark F source.erase) n)
    (labels : Labelled.History ps source target)
    (member : p∈setResidualPositions F n)
    (trace : BetaNodeHistoryPreimage labels p oldPosition) : oldPosition∈F := by
  obtain ⟨name,chosen,_,actual⟩ := old.selected_node_preimage labels member
  have equal := trace.unique actual
  exact equal ▸ chosen
end Lamping.Lambda.Marked
