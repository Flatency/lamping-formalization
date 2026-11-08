import Lamping.Lamping.ActualChainForwardOrder
import Lamping.Lambda.FirstCreatedIncoming
import Lamping.Lambda.LabelOuterBarProvenance
namespace Lamping.AG
open Lambda Lambda.Labelled

/-- The degree policy is applied to actual READ labels, not incoming-node safety. -/
def degreeReadSafe (degree : Label) (value : Option Label) : Prop :=
  ∀ label,value=some label →label.OuterBarsSafe (fun payload=>payload≠degree)

private theorem synchronized_first_false {α β γ : Type} (f : α → γ) (g : β → γ)
    (P : γ → Prop) {xs : List α} {ys : List β} (same : xs.map f=ys.map g) :
    (∀ x∈xs,P (f x)) ∨
    ∃ bs x as cs y ds,xs=bs++x::as ∧ys=cs++y::ds ∧
      bs.length=cs.length ∧bs.map f=cs.map g ∧f x=g y ∧as.map f=ds.map g ∧
      (∀ b∈bs,P (f b)) ∧¬P (f x) := by
  classical
  induction xs generalizing ys with
  | nil => exact Or.inl (by intro x h;cases h)
  | cons x xs ih =>
    cases ys with
    | nil => cases same
    | cons y ys =>
      have head : f x=g y := (List.cons.inj same).1
      have tail : xs.map f=ys.map g := (List.cons.inj same).2
      by_cases good : P (f x)
      · rcases ih tail with all | ⟨bs,z,as,cs,w,ds,l,r,len,front,h,back,safe,bad⟩
        · left;intro z hz
          rcases List.mem_cons.mp hz with eq | mem
          · exact eq ▸ good
          · exact all z mem
        · right
          refine ⟨x::bs,z,as,y::cs,w,ds,by rw [l];rfl,by rw [r];rfl,?_,?_,h,back,?_,bad⟩
          · simp only [List.length_cons];omega
          · simp only [List.map_cons,head,front]
          · intro z hz
            rcases List.mem_cons.mp hz with eq | mem
            · exact eq ▸ good
            · exact safe z mem
      · refine Or.inr ⟨[],x,xs,[],y,ys,rfl,rfl,rfl,rfl,head,tail,?_,good⟩
        intro z h;cases h

private theorem actual_read_cut (chain : PrerequisiteChain t start edges)
    (split : edges=before++edge::after) :
    ∃ reader,PrerequisitePrefix t start before reader ∧
      PrerequisiteReads t reader edge ∧PrerequisiteChain t reader (edge::after) := by
  have mem : edge∈edges := by rw [split];exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨bs,as,reader,other,segment,remainder,read⟩:=chain.split_at_member mem
  obtain ⟨front,back⟩:=chain.first_created_split_unique split other
  subst bs;subst as
  exact ⟨reader,segment,read,remainder⟩

/-- All READ labels are safe, or the first unsafe ordinal is chosen internally
in both actual chains. The returned readers precede any zero-edge binder jumps. -/
theorem actual_first_unsafe_cuts
    {ps : List Path} {source current : LTerm} {leftStart rightStart : Path} {es fs : List Path}
    (labels : History ps source current) (initial : INIT source) (closed : Closed current.erase)
    (leftChain : PrerequisiteChain current leftStart es) (rightChain : PrerequisiteChain current rightStart fs)
    (iso : ChainIncidenceIso (chainSyntaxIncidence current closed es) (chainSyntaxIncidence current closed fs))
    (safe : Option Label →Prop) :
    ((∀ e∈es,safe (current.labelAt e)) ∧(∀ e∈fs,safe (current.labelAt e))) ∨
    ∃ n bs e as cs f ds leftReader rightReader,
      es=bs++e::as ∧fs=cs++f::ds ∧bs.length=n ∧cs.length=n ∧
      es.take n=bs ∧fs.take n=cs ∧es.drop (n+1)=as ∧fs.drop (n+1)=ds ∧
      bs.map current.labelAt=cs.map current.labelAt ∧current.labelAt e=current.labelAt f ∧
      as.map current.labelAt=ds.map current.labelAt ∧
      (∀ b∈bs,safe (current.labelAt b)) ∧(∀ c∈cs,safe (current.labelAt c)) ∧
      ¬safe (current.labelAt e) ∧¬safe (current.labelAt f) ∧
      PrerequisitePrefix current leftStart bs leftReader ∧PrerequisiteReads current leftReader e ∧
      PrerequisiteChain current leftReader (e::as) ∧
      PrerequisitePrefix current rightStart cs rightReader ∧PrerequisiteReads current rightReader f ∧
      PrerequisiteChain current rightReader (f::ds) := by
  have same:=actual_chain_labels_forward labels initial closed leftChain rightChain iso
  rcases synchronized_first_false current.labelAt current.labelAt safe same with all | cut
  · left;refine ⟨all,?_⟩
    intro e mem
    have : current.labelAt e∈es.map current.labelAt := by rw [same];exact List.mem_map.mpr ⟨e,mem,rfl⟩
    obtain ⟨old,inside,equal⟩:=List.mem_map.mp this
    exact equal ▸ all old inside
  · obtain ⟨bs,e,as,cs,f,ds,l,r,len,front,head,back,good,bad⟩:=cut
    obtain ⟨leftReader,lp,lr,lc⟩:=actual_read_cut leftChain l
    obtain ⟨rightReader,rp,rr,rc⟩:=actual_read_cut rightChain r
    have goodRight : ∀ c∈cs,safe (current.labelAt c) := by
      intro c mem
      have : current.labelAt c∈bs.map current.labelAt := by rw [front];exact List.mem_map.mpr ⟨c,mem,rfl⟩
      obtain ⟨b,inside,equal⟩:=List.mem_map.mp this
      exact equal ▸ good b inside
    refine Or.inr ⟨bs.length,bs,e,as,cs,f,ds,leftReader,rightReader,l,r,rfl,len.symm,?_,?_,?_,?_,front,head,back,good,goodRight,bad,?_,lp,lr,lc,rp,rr,rc⟩
    · rw [l];simp
    · rw [r,len];simp
    · rw [l];simp
    · rw [r,len];simp
    · rw [←head];exact bad
end Lamping.AG
