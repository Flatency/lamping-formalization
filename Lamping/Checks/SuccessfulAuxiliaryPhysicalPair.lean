import Lamping.Checks.SuccessfulAuxiliaryPair
import Lamping.Lamping.CanonicalChildDeparture
import Lamping.Lamping.FragmentParentSeparation
import Lamping.Lamping.ActionKeptFragmentComparison
import Lamping.Lamping.FanControlOccurrenceComparison
set_option maxHeartbeats 4000000
namespace Lamping.Checks.SuccessfulAuxiliaryPhysicalPair
open AG Graph Lambda Lambda.Labelled FanSuccessfulReachable

abbrev outerBody : Term := .app (.app (.var 0) (.var 1)) (.var 1)
abbrev innerBody : Term := .app (.var 0) (.var 1)
def embedN (n : (encode 0 inner).N) : (encode 0 term).N := .inr (.inl n)
def embedW (w : (encode 0 inner).W) : (encode 0 term).W := .inl (.inr (.inl w))
def liftFnW (w : (encode 0 fnTerm).W) : (encode 0 term).W := embedW (.inl (.inr (.inl w)))
def liftFBodyW (w : (encode 0 fnBody).W) : (encode 0 fnTerm).W := .inl (.inr w)
def liftXBodyW (w : (encode 0 outerBody).W) : (encode 0 fnBody).W := .inl (.inr w)
def liftInnerN (n : (encode 0 innerBody).N) : (encode 0 term).N :=
  embedN (.inr (.inl (.inr (.inr (.inr (.inl n))))))
def liftInnerW (w : (encode 0 innerBody).W) : (encode 0 outerBody).W := .inl (.inr (.inl w))

def nroot : (encode 0 term).N := outerApp
def kroot : concrete.Kept := ⟨nroot,by constructor <;> intro h <;> cases h⟩
def qroot : actualFanPresentation.Kept := ⟨.inl kroot,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nx : (encode 0 term).N := embedN (.inr (.inl (.inr (.inl ()))))
def kx : concrete.Kept := ⟨nx,by constructor <;> intro h <;> cases h⟩
def qx : actualFanPresentation.Kept := ⟨.inl kx,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nouter : (encode 0 term).N := embedN (.inr (.inl (.inr (.inr (.inl (.inl ()))))))
def kouter : concrete.Kept := ⟨nouter,by constructor <;> intro h <;> cases h⟩
def qouter : actualFanPresentation.Kept := ⟨.inl kouter,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def ninner : (encode 0 term).N := liftInnerN (.inl (.inl ()))
def kinner : concrete.Kept := ⟨ninner,by constructor <;> intro h <;> cases h⟩
def qinner : actualFanPresentation.Kept := ⟨.inl kinner,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nleftVar : (encode 0 term).N := liftInnerN (.inr (.inr ()))
def kleftVar : concrete.Kept := ⟨nleftVar,by constructor <;> intro h <;> cases h⟩
def qleftVar : actualFanPresentation.Kept := ⟨.inl kleftVar,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nleftBra : (encode 0 term).N := liftInnerN (.inl (.inr (.inl ⟨1,rfl⟩)))
def kleftBra : concrete.Kept := ⟨nleftBra,by constructor <;> intro h <;> cases h⟩
def qleftBra : actualFanPresentation.Kept := ⟨.inl kleftBra,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nrightVar : (encode 0 term).N := embedN (.inr (.inl (.inr (.inr (.inr (.inr ()))))))
def krightVar : concrete.Kept := ⟨nrightVar,by constructor <;> intro h <;> cases h⟩
def qrightVar : actualFanPresentation.Kept := ⟨.inl krightVar,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def nrightBra : (encode 0 term).N := embedN (.inr (.inl (.inr (.inr (.inl (.inr (.inl ⟨1,rfl⟩)))))))
def krightBra : concrete.Kept := ⟨nrightBra,by constructor <;> intro h <;> cases h⟩
def qrightBra : actualFanPresentation.Kept := ⟨.inl krightBra,by
  constructor <;> intro h <;> have same:=congrArg Subtype.val (Sum.inl.inj h) <;> cases same⟩

def wroot : (encode 0 term).W := outerFnWire
def oroot : concrete.Outside := ⟨wroot,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vroot : actualFanPresentation.Outside := ⟨.inl (.inl oroot),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wx : (encode 0 term).W := liftFnW (.inr (.inl ()))
def ox : concrete.Outside := ⟨wx,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vx : actualFanPresentation.Outside := ⟨.inl (.inl ox),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wouter : (encode 0 term).W := liftFnW (liftFBodyW (.inr (.inl ())))
def oouter : concrete.Outside := ⟨wouter,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vouter : actualFanPresentation.Outside := ⟨.inl (.inl oouter),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def winner : (encode 0 term).W := liftFnW (liftFBodyW (liftXBodyW (.inr (.inl (.inl ())))))
def oinner : concrete.Outside := ⟨winner,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vinner : actualFanPresentation.Outside := ⟨.inl (.inl oinner),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wleftVar : (encode 0 term).W := liftFnW (liftFBodyW (liftXBodyW (liftInnerW (.inr (.inr (.inl ()))))))
def oleftVar : concrete.Outside := ⟨wleftVar,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vleftVar : actualFanPresentation.Outside := ⟨.inl (.inl oleftVar),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wleftInput : (encode 0 term).W := liftFnW (liftFBodyW (liftXBodyW (liftInnerW (.inr (.inr (.inr ⟨1,rfl⟩))))))
def oleftInput : concrete.Outside := ⟨wleftInput,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vleftInput : actualFanPresentation.Outside := ⟨.inl (.inl oleftInput),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wleftFan : (encode 0 term).W := liftFnW (liftFBodyW (liftXBodyW (.inr (.inl (.inr ⟨1,Or.inr rfl⟩)))))
def oleftFan : concrete.Outside := ⟨wleftFan,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vleftFan : actualFanPresentation.Outside := ⟨.inl (.inl oleftFan),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wrightVar : (encode 0 term).W := embedW (.inl (.inr (.inl (.inl (.inr (.inl (.inr (.inr (.inr (.inl ()))))))))))
def orightVar : concrete.Outside := ⟨wrightVar,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vrightVar : actualFanPresentation.Outside := ⟨.inl (.inl orightVar),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def wrightInput : (encode 0 term).W := embedW (.inl (.inr (.inl (.inl (.inr (.inl (.inr (.inr (.inr (.inr ⟨1,rfl⟩))))))))))
def orightInput : concrete.Outside := ⟨wrightInput,by
  rintro ⟨d,h⟩;simp only [corridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h <;> cases h⟩
def vrightInput : actualFanPresentation.Outside := ⟨.inl (.inl orightInput),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def vctx : actualFanPresentation.Outside := ⟨.inr (.inl false),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

def vbody : actualFanPresentation.Outside := ⟨.inr (.inr true),by
  rintro ⟨d,h⟩;simp only [actualFanLambdaCorridor,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h|h|h|h <;> cases h⟩

noncomputable abbrev lambdaNet := actualFanPresentation.site.reduce
noncomputable def bEnd (e : Endpoint actualCut) : Endpoint concrete.site.reduce :=
  AG.plugLeft actualCut (Schema.beta 0).right.net e
noncomputable def fEnd (e : Endpoint cut2) : Endpoint lambdaNet :=
  AG.plugLeft cut2 (Schema.fanAction .lam 0 1 (by decide)).right.net e

theorem beta_root : concrete.site.reduce.wire (bEnd (.inr (.inl (.inl (.inl ())))))=bEnd (.inl ⟨kroot,appCtx⟩) :=
  beta_lift_wire (.inr (.inl (.inl (.inl ())))) (.inl ⟨kroot,appCtx⟩) rfl
theorem lambda_root : lambdaNet.wire (fEnd (.inr (.inl (.inl (.inl ())))))=fEnd (.inl ⟨qroot,appCtx⟩) :=
  action2_lift_wire (.inr (.inl (.inl (.inl ())))) (.inl ⟨qroot,appCtx⟩) beta_root

theorem beta_rootfn : concrete.site.reduce.wire (bEnd (.inl ⟨kroot,.inl ()⟩))=bEnd (.inr (.inr (oroot,false))) :=
  beta_lift_wire (.inl ⟨kroot,.inl ()⟩) (.inr (.inr (oroot,false))) rfl
theorem lambda_rootfn : lambdaNet.wire (fEnd (.inl ⟨qroot,.inl ()⟩))=fEnd (.inr (.inr (vroot,false))) :=
  action2_lift_wire (.inl ⟨qroot,.inl ()⟩) (.inr (.inr (vroot,false))) beta_rootfn

theorem beta_context : concrete.site.reduce.wire (bEnd (.inr (.inr (oroot,true))))=bEnd (.inr (.inl (.inr (.inl false)))) :=
  beta_lift_wire (.inr (.inr (oroot,true))) (.inr (.inl (.inr (.inl false)))) rfl
theorem lambda_context : lambdaNet.wire (fEnd (.inr (.inr (vroot,true))))=fEnd (.inr (.inr (vctx,false))) :=
  action2_lift_wire (.inr (.inr (vroot,true))) (.inr (.inr (vctx,false))) beta_context

theorem beta_body : concrete.site.reduce.wire (bEnd (.inr (.inl (.inr (.inr true)))))=bEnd (.inr (.inr (ox,false))) :=
  beta_lift_wire (.inr (.inl (.inr (.inr true)))) (.inr (.inr (ox,false))) rfl
theorem lambda_body : lambdaNet.wire (fEnd (.inr (.inr (vbody,false))))=fEnd (.inr (.inr (vx,false))) :=
  action2_lift_wire (.inr (.inr (vbody,false))) (.inr (.inr (vx,false))) beta_body

theorem beta_x : concrete.site.reduce.wire (bEnd (.inr (.inr (ox,true))))=bEnd (.inl ⟨kx,.inl ()⟩) :=
  beta_lift_wire (.inr (.inr (ox,true))) (.inl ⟨kx,.inl ()⟩) rfl
theorem lambda_x : lambdaNet.wire (fEnd (.inr (.inr (vx,true))))=fEnd (.inl ⟨qx,.inl ()⟩) :=
  action2_lift_wire (.inr (.inr (vx,true))) (.inl ⟨qx,.inl ()⟩) beta_x

theorem beta_xbody : concrete.site.reduce.wire (bEnd (.inl ⟨kx,lamBody⟩))=bEnd (.inr (.inr (oouter,false))) :=
  beta_lift_wire (.inl ⟨kx,lamBody⟩) (.inr (.inr (oouter,false))) rfl
theorem lambda_xbody : lambdaNet.wire (fEnd (.inl ⟨qx,lamBody⟩))=fEnd (.inr (.inr (vouter,false))) :=
  action2_lift_wire (.inl ⟨qx,lamBody⟩) (.inr (.inr (vouter,false))) beta_xbody

theorem beta_outer : concrete.site.reduce.wire (bEnd (.inr (.inr (oouter,true))))=bEnd (.inl ⟨kouter,appCtx⟩) :=
  beta_lift_wire (.inr (.inr (oouter,true))) (.inl ⟨kouter,appCtx⟩) rfl
theorem lambda_outer : lambdaNet.wire (fEnd (.inr (.inr (vouter,true))))=fEnd (.inl ⟨qouter,appCtx⟩) :=
  action2_lift_wire (.inr (.inr (vouter,true))) (.inl ⟨qouter,appCtx⟩) beta_outer

theorem beta_outerfn : concrete.site.reduce.wire (bEnd (.inl ⟨kouter,.inl ()⟩))=bEnd (.inr (.inr (oinner,false))) :=
  beta_lift_wire (.inl ⟨kouter,.inl ()⟩) (.inr (.inr (oinner,false))) rfl
theorem lambda_outerfn : lambdaNet.wire (fEnd (.inl ⟨qouter,.inl ()⟩))=fEnd (.inr (.inr (vinner,false))) :=
  action2_lift_wire (.inl ⟨qouter,.inl ()⟩) (.inr (.inr (vinner,false))) beta_outerfn

theorem beta_inner : concrete.site.reduce.wire (bEnd (.inr (.inr (oinner,true))))=bEnd (.inl ⟨kinner,appCtx⟩) :=
  beta_lift_wire (.inr (.inr (oinner,true))) (.inl ⟨kinner,appCtx⟩) rfl
theorem lambda_inner : lambdaNet.wire (fEnd (.inr (.inr (vinner,true))))=fEnd (.inl ⟨qinner,appCtx⟩) :=
  action2_lift_wire (.inr (.inr (vinner,true))) (.inl ⟨qinner,appCtx⟩) beta_inner

theorem beta_innerarg : concrete.site.reduce.wire (bEnd (.inl ⟨kinner,appArg⟩))=bEnd (.inr (.inr (oleftVar,false))) :=
  beta_lift_wire (.inl ⟨kinner,appArg⟩) (.inr (.inr (oleftVar,false))) rfl
theorem lambda_innerarg : lambdaNet.wire (fEnd (.inl ⟨qinner,appArg⟩))=fEnd (.inr (.inr (vleftVar,false))) :=
  action2_lift_wire (.inl ⟨qinner,appArg⟩) (.inr (.inr (vleftVar,false))) beta_innerarg

theorem beta_leftvaraux : concrete.site.reduce.wire (bEnd (.inr (.inr (oleftVar,true))))=bEnd (.inl ⟨kleftVar,.inr ()⟩) :=
  beta_lift_wire (.inr (.inr (oleftVar,true))) (.inl ⟨kleftVar,.inr ()⟩) rfl
theorem lambda_leftvaraux : lambdaNet.wire (fEnd (.inr (.inr (vleftVar,true))))=fEnd (.inl ⟨qleftVar,.inr ()⟩) :=
  action2_lift_wire (.inr (.inr (vleftVar,true))) (.inl ⟨qleftVar,.inr ()⟩) beta_leftvaraux

theorem beta_leftvar : concrete.site.reduce.wire (bEnd (.inl ⟨kleftVar,.inl ()⟩))=bEnd (.inr (.inr (oleftInput,true))) :=
  beta_lift_wire (.inl ⟨kleftVar,.inl ()⟩) (.inr (.inr (oleftInput,true))) rfl
theorem lambda_leftvar : lambdaNet.wire (fEnd (.inl ⟨qleftVar,.inl ()⟩))=fEnd (.inr (.inr (vleftInput,true))) :=
  action2_lift_wire (.inl ⟨qleftVar,.inl ()⟩) (.inr (.inr (vleftInput,true))) beta_leftvar

theorem beta_leftbraaux : concrete.site.reduce.wire (bEnd (.inr (.inr (oleftInput,false))))=bEnd (.inl ⟨kleftBra,.inr ()⟩) :=
  beta_lift_wire (.inr (.inr (oleftInput,false))) (.inl ⟨kleftBra,.inr ()⟩) rfl
theorem lambda_leftbraaux : lambdaNet.wire (fEnd (.inr (.inr (vleftInput,false))))=fEnd (.inl ⟨qleftBra,.inr ()⟩) :=
  action2_lift_wire (.inr (.inr (vleftInput,false))) (.inl ⟨qleftBra,.inr ()⟩) beta_leftbraaux

theorem beta_leftbra : concrete.site.reduce.wire (bEnd (.inl ⟨kleftBra,.inl ()⟩))=bEnd (.inr (.inr (oleftFan,true))) :=
  beta_lift_wire (.inl ⟨kleftBra,.inl ()⟩) (.inr (.inr (oleftFan,true))) rfl
theorem lambda_leftbra : lambdaNet.wire (fEnd (.inl ⟨qleftBra,.inl ()⟩))=fEnd (.inr (.inr (vleftFan,true))) :=
  action2_lift_wire (.inl ⟨qleftBra,.inl ()⟩) (.inr (.inr (vleftFan,true))) beta_leftbra

theorem beta_leftfan : concrete.site.reduce.wire (bEnd (.inr (.inr (oleftFan,false))))=bEnd (.inl ⟨fanKept,.inr false⟩) :=
  beta_lift_wire (.inr (.inr (oleftFan,false))) (.inl ⟨fanKept,.inr false⟩) rfl
theorem lambda_leftfan : lambdaNet.wire (fEnd (.inr (.inr (vleftFan,false))))=fEnd (.inr (.inl (.inr (.inl false)))) :=
  action2_lift_wire (.inr (.inr (vleftFan,false))) (.inr (.inl (.inr (.inl false)))) beta_leftfan

theorem beta_outerarg : concrete.site.reduce.wire (bEnd (.inl ⟨kouter,appArg⟩))=bEnd (.inr (.inr (orightVar,false))) :=
  beta_lift_wire (.inl ⟨kouter,appArg⟩) (.inr (.inr (orightVar,false))) rfl
theorem lambda_outerarg : lambdaNet.wire (fEnd (.inl ⟨qouter,appArg⟩))=fEnd (.inr (.inr (vrightVar,false))) :=
  action2_lift_wire (.inl ⟨qouter,appArg⟩) (.inr (.inr (vrightVar,false))) beta_outerarg

theorem beta_rightvaraux : concrete.site.reduce.wire (bEnd (.inr (.inr (orightVar,true))))=bEnd (.inl ⟨krightVar,.inr ()⟩) :=
  beta_lift_wire (.inr (.inr (orightVar,true))) (.inl ⟨krightVar,.inr ()⟩) rfl
theorem lambda_rightvaraux : lambdaNet.wire (fEnd (.inr (.inr (vrightVar,true))))=fEnd (.inl ⟨qrightVar,.inr ()⟩) :=
  action2_lift_wire (.inr (.inr (vrightVar,true))) (.inl ⟨qrightVar,.inr ()⟩) beta_rightvaraux

theorem beta_rightvar : concrete.site.reduce.wire (bEnd (.inl ⟨krightVar,.inl ()⟩))=bEnd (.inr (.inr (orightInput,true))) :=
  beta_lift_wire (.inl ⟨krightVar,.inl ()⟩) (.inr (.inr (orightInput,true))) rfl
theorem lambda_rightvar : lambdaNet.wire (fEnd (.inl ⟨qrightVar,.inl ()⟩))=fEnd (.inr (.inr (vrightInput,true))) :=
  action2_lift_wire (.inl ⟨qrightVar,.inl ()⟩) (.inr (.inr (vrightInput,true))) beta_rightvar

theorem beta_rightbraaux : concrete.site.reduce.wire (bEnd (.inr (.inr (orightInput,false))))=bEnd (.inl ⟨krightBra,.inr ()⟩) :=
  beta_lift_wire (.inr (.inr (orightInput,false))) (.inl ⟨krightBra,.inr ()⟩) rfl
theorem lambda_rightbraaux : lambdaNet.wire (fEnd (.inr (.inr (vrightInput,false))))=fEnd (.inl ⟨qrightBra,.inr ()⟩) :=
  action2_lift_wire (.inr (.inr (vrightInput,false))) (.inl ⟨qrightBra,.inr ()⟩) beta_rightbraaux

theorem beta_rightbra : concrete.site.reduce.wire (bEnd (.inl ⟨krightBra,.inl ()⟩))=bEnd (.inl ⟨fanKept,.inr true⟩) :=
  beta_lift_wire (.inl ⟨krightBra,.inl ()⟩) (.inl ⟨fanKept,.inr true⟩) rfl
theorem lambda_rightbra : lambdaNet.wire (fEnd (.inl ⟨qrightBra,.inl ()⟩))=fEnd (.inr (.inl (.inr (.inl true)))) :=
  action2_lift_wire (.inl ⟨qrightBra,.inl ()⟩) (.inr (.inl (.inr (.inl true)))) beta_rightbra

theorem lambda_context_body : lambdaNet.wire (fEnd (.inr (.inr (vctx,true))))=
    fEnd (.inr (.inr (vbody,true))) := by
  exact action2_lift_wire (.inr (.inr (vctx,true))) (.inr (.inr (vbody,true))) rfl

noncomputable def outerEdges : List (Endpoint lambdaNet) := [
  fEnd (.inr (.inl (.inl (.inl ())))),fEnd (.inl ⟨qroot,.inl ()⟩),
  fEnd (.inr (.inr (vroot,true))),fEnd (.inr (.inr (vctx,true))),
  fEnd (.inr (.inr (vbody,false))),fEnd (.inr (.inr (vx,true))),
  fEnd (.inl ⟨qx,lamBody⟩),fEnd (.inr (.inr (vouter,true)))]

theorem outerLabels (a : Context) : Labelling lambdaNet outerEdges a a := by
  apply Labelling.cons (by rw [lambda_root];exact LabelledTurn.node (g:=lambdaNet) (.inl qroot) appCtx (.inl ()) (.direct (.appFun a)))
  apply Labelling.cons (by rw [lambda_rootfn];exact .transparent _ false a)
  apply Labelling.cons (by rw [lambda_context];exact .transparent _ false a)
  apply Labelling.cons (by rw [lambda_context_body];exact .transparent _ true a)
  apply Labelling.cons (by rw [lambda_body];exact .transparent _ false a)
  apply Labelling.cons (by rw [lambda_x];exact LabelledTurn.node (g:=lambdaNet) (.inl qx) (Sum.inl ()) lamBody (.direct (.lamBody a)))
  exact .cons (by rw [lambda_xbody];exact .transparent _ false a) (.single _ a)

theorem outerWord : accessWord lambdaNet outerEdges=[.fn,.body] := rfl

theorem outerFinish : outerEdges.getLast?=some (lambdaNet.wire (fEnd (.inl ⟨qouter,appCtx⟩))) := by
  have inverse:=congrArg lambdaNet.wire lambda_outer
  simp only [Pairing.involutive] at inverse
  simpa only [outerEdges,List.getLast?_cons_cons,List.getLast?_singleton] using congrArg some inverse

noncomputable def front (b : Bool) : Endpoint lambdaNet := .inr (.inr (.inr (.inl b),true))
theorem front_finish (b : Bool) : lambdaNet.wire (front b)=.inl ⟨.inr (.inl b),.inl ()⟩ := rfl

abbrev pairContext := Context.empty.cons (.pair .empty .empty)
private theorem empty_replace (n : Nat) : Context.empty.replace n Context.empty=Context.empty := by
  ext k;simp [Context.replace]
private theorem emptyCro : Traversal 1 (.op .cro) (.inr ()) (.inl ()) Context.empty Context.empty := by
  simpa only [Context.cons_empty,empty_replace] using (Traversal.direct (Passage.cro (i:=1) Context.empty Context.empty))
private theorem emptyBra : Traversal 0 (.op .bra) (.inr ()) (.inl ()) Context.empty pairContext := by
  simpa only [Context.cons_empty,Context.replace_zero] using (Traversal.direct (Passage.bra (i:=0) Context.empty Context.empty .empty .empty))

noncomputable def leftTail : List (Endpoint lambdaNet) := [
  fEnd (.inl ⟨qouter,.inl ()⟩),fEnd (.inr (.inr (vinner,true))),
  fEnd (.inl ⟨qinner,appArg⟩),fEnd (.inr (.inr (vleftVar,true))),
  fEnd (.inl ⟨qleftVar,.inl ()⟩),fEnd (.inr (.inr (vleftInput,false))),
  fEnd (.inl ⟨qleftBra,.inl ()⟩),fEnd (.inr (.inr (vleftFan,false))),front false]

theorem leftTailLabels : Labelling lambdaNet leftTail Context.empty pairContext := by
  apply Labelling.cons (by rw [lambda_outerfn];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [lambda_inner];exact LabelledTurn.node (g:=lambdaNet) (.inl qinner) appCtx appArg (.direct (.appArg Context.empty)))
  apply Labelling.cons (by rw [lambda_innerarg];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [lambda_leftvaraux];exact LabelledTurn.node (g:=lambdaNet) (.inl qleftVar) _ _ emptyCro)
  apply Labelling.cons (by rw [lambda_leftvar];exact .transparent _ true Context.empty)
  apply Labelling.cons (by rw [lambda_leftbraaux];exact LabelledTurn.node (g:=lambdaNet) (.inl qleftBra) _ _ emptyBra)
  apply Labelling.cons (by rw [lambda_leftbra];exact .transparent _ true pairContext)
  exact .cons (by rw [lambda_leftfan];exact .transparent _ false pairContext) (.single _ _)

noncomputable def rightTail : List (Endpoint lambdaNet) := [
  fEnd (.inl ⟨qouter,appArg⟩),fEnd (.inr (.inr (vrightVar,true))),
  fEnd (.inl ⟨qrightVar,.inl ()⟩),fEnd (.inr (.inr (vrightInput,false))),
  fEnd (.inl ⟨qrightBra,.inl ()⟩),front true]

theorem rightTailLabels : Labelling lambdaNet rightTail Context.empty pairContext := by
  apply Labelling.cons (by rw [lambda_outerarg];exact .transparent _ false Context.empty)
  apply Labelling.cons (by rw [lambda_rightvaraux];exact LabelledTurn.node (g:=lambdaNet) (.inl qrightVar) _ _ emptyCro)
  apply Labelling.cons (by rw [lambda_rightvar];exact .transparent _ true Context.empty)
  apply Labelling.cons (by rw [lambda_rightbraaux];exact LabelledTurn.node (g:=lambdaNet) (.inl qrightBra) _ _ emptyBra)
  exact .cons (by rw [lambda_rightbra];exact .transparent _ false pairContext) (.single _ _)

noncomputable def leftEdges := outerEdges++leftTail
noncomputable def rightEdges := outerEdges++rightTail

theorem leftLabels : Labelling lambdaNet leftEdges Context.empty pairContext := by
  exact (outerLabels Context.empty).append_seam leftTailLabels (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans outerFinish)
    have hf:=Option.some.inj first
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=lambdaNet) (.inl qouter) appCtx (.inl ()) (.direct (.appFun Context.empty)))

theorem rightLabels : Labelling lambdaNet rightEdges Context.empty pairContext := by
  exact (outerLabels Context.empty).append_seam rightTailLabels (by
    intro e f last first
    have he:=Option.some.inj (last.symm.trans outerFinish)
    have hf:=Option.some.inj first
    subst e;subst f
    rw [Pairing.involutive]
    exact LabelledTurn.node (g:=lambdaNet) (.inl qouter) appCtx appArg (.direct (.appArg Context.empty)))

theorem leftWord : accessWord lambdaNet leftEdges=FanSuccessfulChains.left := by
  rw [leftEdges,accessWord_append lambdaNet _ _ (outerLabels Context.empty).nonempty,outerWord]
  rfl
theorem rightWord : accessWord lambdaNet rightEdges=FanSuccessfulChains.right := by
  rw [rightEdges,accessWord_append lambdaNet _ _ (outerLabels Context.empty).nonempty,outerWord]
  rfl

theorem leftFinish : leftEdges.getLast?=some (lambdaNet.wire (.inl ⟨.inr (.inl false),.inl ()⟩)) := by
  rw [leftEdges,List.getLast?_append]
  have inverse:=congrArg lambdaNet.wire (front_finish false)
  simp only [Pairing.involutive] at inverse
  simpa only [leftTail,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or] using congrArg some inverse

theorem rightFinish : rightEdges.getLast?=some (lambdaNet.wire (.inl ⟨.inr (.inl true),.inl ()⟩)) := by
  rw [rightEdges,List.getLast?_append]
  have inverse:=congrArg lambdaNet.wire (front_finish true)
  simp only [Pairing.involutive] at inverse
  simpa only [rightTail,List.getLast?_cons_cons,List.getLast?_singleton,Option.some_or] using congrArg some inverse

noncomputable def leftParent : RootAccess lambdaNet (.inl ()) := by
  let flow:=Classical.choose lambda_certified
  exact ⟨leftEdges,⟨⟨⟨Context.empty,pairContext,leftLabels⟩,
    leftLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [leftFinish];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
noncomputable def rightParent : RootAccess lambdaNet (.inl ()) := by
  let flow:=Classical.choose lambda_certified
  exact ⟨rightEdges,⟨⟨⟨Context.empty,pairContext,rightLabels⟩,
    rightLabels.root_forward_of_flow flow (.inl ()) rfl rfl⟩,rfl,⟨.lam,by
      unfold accessKind;rw [rightFinish];simp only [Option.bind_some,Pairing.involutive];rfl⟩⟩⟩
#print axioms leftParent
#print axioms rightParent
#print axioms leftWord
#print axioms rightWord

def copiedLambda (b : Bool) : fanCro.Kept := ⟨.inr (.inl b),by constructor <;> intro h <;> cases h⟩
noncomputable def chosenParent (b : Bool) : RootAccess lambdaNet (.inl ()) :=
  if b then rightParent else leftParent

theorem chosenWord (b : Bool) : accessWord lambdaNet (chosenParent b).val=
    if b then FanSuccessfulChains.right else FanSuccessfulChains.left := by
  cases b
  · exact leftWord
  · exact rightWord

theorem chosenFinish (b : Bool) : (chosenParent b).val.getLast?=
    some (lambdaNet.wire (.inl ⟨.inr (.inl b),.inl ()⟩)) := by
  cases b
  · exact leftFinish
  · exact rightFinish

noncomputable def sourceParent (b : Bool) : RootAccess fanCro.site.net (.inl ()) :=
  fanCro.sourceIso.rootAccessBij (.inl ()) (chosenParent b)

theorem sourceWord (b : Bool) : accessWord fanCro.site.net (sourceParent b).val=
    if b then FanSuccessfulChains.right else FanSuccessfulChains.left :=
  (fanCro.sourceIso.accessWord (chosenParent b).val).trans (chosenWord b)

theorem sourceFinish (b : Bool) : (sourceParent b).val.getLast?=
    some (fanCro.site.net.wire (.inl ⟨.inl (copiedLambda b),.inl ()⟩)) := by
  change ((chosenParent b).val.map fanCro.sourceIso.ends).getLast?=_
  rw [List.getLast?_map,chosenFinish]
  simp only [Option.map_some]
  apply congrArg some
  rw [fanCro.sourceIso.wiring]
  apply congrArg fanCro.site.net.wire
  apply fanCro.sourceIso.symm.ends.injective
  change fanCro.sourceIso.ends.invFun (fanCro.sourceIso.ends.toFun (.inl ⟨.inr (.inl b),.inl ()⟩)) =
    fanCro.sourceIso.ends.invFun (.inl ⟨.inl (copiedLambda b),.inl ()⟩)
  rw [fanCro.sourceIso.ends.left_inv]
  rfl

def parentPosition (b : Bool) : Position current.erase :=
  ⟨if b then FanSuccessfulChains.right else FanSuccessfulChains.left,by cases b <;> rfl⟩
noncomputable def targetParent (b : Bool) : RootAccess fanCro.site.reduce (.inl ()) :=
  Classical.choose (Matches.observation fanCro.site.reduce actual_final_matches (parentPosition b))

theorem targetWord (b : Bool) : accessWord fanCro.site.reduce (targetParent b).val=
    if b then FanSuccessfulChains.right else FanSuccessfulChains.left :=
  (Classical.choose_spec (Matches.observation fanCro.site.reduce actual_final_matches (parentPosition b))).1

theorem targetFinish (b : Bool) : (targetParent b).val.getLast?=
    some (fanCro.site.reduce.wire (.inl ⟨.inl (copiedLambda b),.inl ()⟩)) := by
  obtain ⟨port,finish⟩ := fanCro.site.fan_control_access_kept (Or.inr (Or.inl rfl)) (targetParent b)
  obtain ⟨a,c,labels⟩ := (targetParent b).property.1.1
  obtain ⟨principal⟩ := fanCro.site.actionPrincipal_exists
  obtain ⟨flow,_,_,_,_⟩ := lambda_certified
  have normalized := fanCro.site.action_kept_canonical_access (.fan .cro 0 1 (by decide))
    (fanCro.sourceIso.flowBalance flow) (.inl ()) rfl actual_source_matches principal
    (sourceParent b) (targetParent b) ((sourceWord b).trans (targetWord b).symm)
    port.1 port.2 finish labels
  have wireEq := Option.some.inj ((sourceFinish b).symm.trans normalized.2.2)
  have endEq := congrArg fanCro.site.net.wire wireEq
  simp only [Pairing.involutive] at endEq
  rcases port with ⟨node,p⟩
  have nodeEq : copiedLambda b=node := Sum.inl.inj (congrArg Sigma.fst (Sum.inl.inj endEq))
  subst node
  have portEq : (Sum.inl () : Port (fanCro.kept (copiedLambda b)).sort)=p :=
    eq_of_heq (Sigma.mk.inj (Sum.inl.inj endEq)).2
  subst p
  exact finish
#print axioms sourceFinish
#print axioms targetFinish


open FanSuccessfulChains hiding current original
abbrev leftBodyEdge := sourceEdge [leftLabel,functionLabel] (.lamBody leftLabel) callerBody
abbrev rightBodyEdge := sourceEdge [rightLabel,functionLabel] (.lamBody rightLabel) callerBody

theorem copiedLambda_different : copiedLambda false≠copiedLambda true := by
  intro same
  have impossible:=congrArg Subtype.val same
  cases impossible

/-- The two real parent nodes, rather than labels or non-isomorphism, separate
both literal BODY pieces, for arbitrary lawful physical fragment choices. -/
theorem actual_body_pieces_different
    (sourceLeft : SourceEdgeFragment current fanCro.site.net (.inl ()) leftBodyEdge leftBody)
    (targetLeft : SourceEdgeFragment current fanCro.site.reduce (.inl ()) leftBodyEdge leftBody)
    (sourceRight : SourceEdgeFragment current fanCro.site.net (.inl ()) rightBodyEdge rightBody)
    (targetRight : SourceEdgeFragment current fanCro.site.reduce (.inl ()) rightBodyEdge rightBody) :
    sourceLeft.segments≠sourceRight.segments ∧targetLeft.segments≠targetRight.segments := by
  have oldLeft : leftBody=accessWord fanCro.site.net (sourceParent false).val++[.body] := by
    rw [sourceWord];rfl
  have oldRight : rightBody=accessWord fanCro.site.net (sourceParent true).val++[.body] := by
    rw [sourceWord];rfl
  have newLeft : leftBody=accessWord fanCro.site.reduce (targetParent false).val++[.body] := by
    rw [targetWord];rfl
  have newRight : rightBody=accessWord fanCro.site.reduce (targetParent true).val++[.body] := by
    rw [targetWord];rfl
  constructor
  · exact sourceLeft.ne_of_parent_nodes actual_source_matches sourceRight
      (SourceDeparture.body (label:=leftLabel) (body:=callerBody))
      (SourceDeparture.body (label:=rightLabel) (body:=callerBody))
      (sourceParent false) (sourceParent true) oldLeft oldRight
      (.inl (copiedLambda false)) (.inl (copiedLambda true)) (.inl ()) (.inl ())
      (sourceFinish false) (sourceFinish true) (fun h=>copiedLambda_different (Sum.inl.inj h))
  · exact targetLeft.ne_of_parent_nodes actual_final_matches targetRight
      (SourceDeparture.body (label:=leftLabel) (body:=callerBody))
      (SourceDeparture.body (label:=rightLabel) (body:=callerBody))
      (targetParent false) (targetParent true) newLeft newRight
      (.inl (copiedLambda false)) (.inl (copiedLambda true)) (.inl ()) (.inl ())
      (targetFinish false) (targetFinish true) (fun h=>copiedLambda_different (Sum.inl.inj h))

theorem arbitrary_body_occurrences_different
    (sourceLeft : OccurrenceFragment current fanCro.site.net (.inl ()) leftBody)
    (targetLeft : OccurrenceFragment current fanCro.site.reduce (.inl ()) leftBody)
    (sourceRight : OccurrenceFragment current fanCro.site.net (.inl ()) rightBody)
    (targetRight : OccurrenceFragment current fanCro.site.reduce (.inl ()) rightBody) :
    sourceLeft.fragment.segments≠sourceRight.fragment.segments ∧
    targetLeft.fragment.segments≠targetRight.fragment.segments := by
  rcases sourceLeft with ⟨sl,el,cl,ol,fl⟩
  rcases targetLeft with ⟨tl,etl,ctl,otl,ftl⟩
  rcases sourceRight with ⟨sr,er,cr,orr,fr⟩
  rcases targetRight with ⟨tr,etr,ctr,otr,ftr⟩
  obtain ⟨rfl,rfl,rfl⟩:=ol.same_occurrence left_body_occurrence
  obtain ⟨rfl,rfl,rfl⟩:=otl.same_occurrence left_body_occurrence
  obtain ⟨rfl,rfl,rfl⟩:=orr.same_occurrence right_body_occurrence
  obtain ⟨rfl,rfl,rfl⟩:=otr.same_occurrence right_body_occurrence
  exact actual_body_pieces_different fl ftl fr ftr

theorem actual_selections :
    Nonempty (OccurrenceFragmentSelection current fanCro.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current fanCro.site.reduce (.inl ())) :=
  ⟨actual_source_matches.occurrence_fragment_selection targetClosed,
    actual_final_matches.occurrence_fragment_selection targetClosed⟩

/-- This is the successful-domain pair's local Aux conclusion. The physical
inequalities above are independently established from real parent paths. -/
theorem pair_auxiliary_conclusion :
    ¬(SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.source current SuccessfulAuxiliaryPair.leftEdge)
      (SyntaxIncidence.source current SuccessfulAuxiliaryPair.rightEdge) ∧
    SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.target current targetClosed SuccessfulAuxiliaryPair.leftEdge)
      (SyntaxIncidence.target current targetClosed SuccessfulAuxiliaryPair.rightEdge)) := by
  exact fun h=>SuccessfulAuxiliaryPair.source_endpoints_not_successfully_isomorphic h.1

/-- One original INIT, actual labelled history and three-rule trace supply
nonempty legal choices at two distinct, equally labelled auxiliary positions.
Their four endpoints genuinely have successful chains. This is a local pair
regression, not a theorem of whole AuxiliarySeparation or Joint preservation. -/
theorem actual_successful_physical_pair :
    INIT original ∧Closed original.erase ∧History [[.fn]] original current ∧
    GraphTrace (ActualNet.initial term) (ActualNet.ofNet fanCro.site.reduce)
      [.beta 0,.fanAction .lam 0 1 (by decide),.fanAction .cro 0 1 (by decide)] ∧
    Matches fanCro.site.net (.inl ()) current.erase ∧Matches fanCro.site.reduce (.inl ()) current.erase ∧
    Nonempty (OccurrenceFragmentSelection current fanCro.site.net (.inl ())) ∧
    Nonempty (OccurrenceFragmentSelection current fanCro.site.reduce (.inl ())) ∧
    AuxiliaryAt current leftBody ∧AuxiliaryAt current rightBody ∧
    SyntaxIncidence.label current SuccessfulAuxiliaryPair.leftEdge=
      SyntaxIncidence.label current SuccessfulAuxiliaryPair.rightEdge ∧
    EndpointChain current (SyntaxIncidence.source current SuccessfulAuxiliaryPair.leftEdge) FanSuccessfulChains.leftEdges ∧
    EndpointChain current (SyntaxIncidence.source current SuccessfulAuxiliaryPair.rightEdge) FanSuccessfulChains.rightEdges ∧
    EndpointChain current (SyntaxIncidence.target current targetClosed SuccessfulAuxiliaryPair.leftEdge) leftBodyEdges ∧
    EndpointChain current (SyntaxIncidence.target current targetClosed SuccessfulAuxiliaryPair.rightEdge) rightBodyEdges ∧
    (∀ (sl : OccurrenceFragment current fanCro.site.net (.inl ()) leftBody)
       (tl : OccurrenceFragment current fanCro.site.reduce (.inl ()) leftBody)
       (sr : OccurrenceFragment current fanCro.site.net (.inl ()) rightBody)
       (tr : OccurrenceFragment current fanCro.site.reduce (.inl ()) rightBody),
      sl.fragment.segments≠sr.fragment.segments ∧tl.fragment.segments≠tr.fragment.segments) ∧
    ¬(SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.source current SuccessfulAuxiliaryPair.leftEdge)
      (SyntaxIncidence.source current SuccessfulAuxiliaryPair.rightEdge) ∧
    SuccessfulEndpointIso current targetClosed
      (SyntaxIncidence.target current targetClosed SuccessfulAuxiliaryPair.leftEdge)
      (SyntaxIncidence.target current targetClosed SuccessfulAuxiliaryPair.rightEdge)) := by
  obtain ⟨sourceExists,targetExists⟩:=actual_selections
  obtain ⟨ls,rs,lt,rt⟩:=SuccessfulAuxiliaryPair.four_successful_endpoints
  exact ⟨initial,sourceClosed,actualHistory,actual_three_step_trace,actual_source_matches,
    actual_final_matches,sourceExists,targetExists,SuccessfulAuxiliaryPair.left_aux,
    SuccessfulAuxiliaryPair.right_aux,SuccessfulAuxiliaryPair.equal_label,ls,rs,lt,rt,
    arbitrary_body_occurrences_different,pair_auxiliary_conclusion⟩
#print axioms copiedLambda_different
#print axioms actual_body_pieces_different
#print axioms arbitrary_body_occurrences_different
#print axioms actual_selections
#print axioms pair_auxiliary_conclusion
#print axioms actual_successful_physical_pair
end Lamping.Checks.SuccessfulAuxiliaryPhysicalPair