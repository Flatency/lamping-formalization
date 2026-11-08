import Lamping.Lambda.LabelRoutes
namespace Lamping.Lambda.Labelled

/-- The four source-lambda-graph turns occurring in labelled beta paths,
with their reverse turns for a traversal in the opposite direction. -/
inductive SourceTurn : SourcePort → SourcePort → Prop where
  | appOver (l) : SourceTurn (.appContext l) (.appFn l)
  | lamOver (l) : SourceTurn (.lamContext l) (.lamBody l)
  | lamUnder (l) : SourceTurn (.lamBind l) (.lamContext l)
  | appUnder (l) : SourceTurn (.appFn l) (.appArg l)
  | symm : SourceTurn a b → SourceTurn b a

/-- One oriented traversal is an actual edge in the fixed initial term. -/
inductive SourceTraverse (edges : List SourceEdge) : SourcePort → OrientedAtom → SourcePort → Prop where
  | forward (member : e∈edges) (atomic : e.atom=Label.atom n) :
      SourceTraverse edges e.fromPort ⟨n,false⟩ e.toPort
  | backward (member : e∈edges) (atomic : e.atom=Label.atom n) :
      SourceTraverse edges e.toPort ⟨n,true⟩ e.fromPort

theorem SourceTraverse.flip (h : SourceTraverse edges a e b) : SourceTraverse edges b e.flip a := by
  cases h with
  | forward member atomic => exact .backward member atomic
  | backward member atomic => exact .forward member atomic

/-- Nonempty walks retain every edge orientation and every intervening port
turn; they cannot identify context and binding ports. -/
inductive SourceWalk (edges : List SourceEdge) : SourcePort → EdgeWord → SourcePort → Prop where
  | edge : SourceTraverse edges a e b → SourceWalk edges a [e] b
  | join : SourceWalk edges a p b → SourceTurn b c → SourceWalk edges c q d →
      SourceWalk edges a (p++q) d

theorem SourceWalk.reverse (h : SourceWalk edges a p b) : SourceWalk edges b (EdgeWord.reverse p) a := by
  induction h with
  | edge h => exact .edge h.flip
  | join hp turn hq ihp ihq =>
    rw [EdgeWord.reverse_append]
    exact .join ihq (.symm turn) ihp

/-- AG6.2.2 path soundness from the genuine generated-label endpoint geometry. -/
theorem SourceRoute.walk (h : SourceRoute edges a l b) : SourceWalk edges a l.edgeWord b := by
  induction h with
  | atom member atomic => exact .edge (.forward member atomic)
  | over left degree right hl hd hr =>
    simp only [Label.edgeWord_concat,Label.edgeWord_over]
    exact .join (.join hl (.appOver _) hd) (.lamOver _) hr
  | under left degree right hl hd hr =>
    simp only [Label.edgeWord_concat,Label.edgeWord_under]
    exact .join (.join hl (.lamUnder _) hd.reverse) (.appUnder _) hr

/-- Every current redex degree is an actual path in the original INIT term,
from an original application's function port to an original lambda context. -/
theorem TermRoutes.degree_walk (h : TermRoutes edges env ctx t) (degree : t.degreeAt p=some alpha) :
    ∃ appId lamId, SourceWalk edges (.appFn appId) alpha.edgeWord (.lamContext lamId) := by
  induction p generalizing env ctx t with
  | nil =>
    cases h with
    | var => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | lam => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
    | app route fn arg =>
      cases fn with
      | var => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | app => simp [LTerm.degreeAt,LTerm.subterm,LTerm.degree] at degree
      | lam root body =>
        simp only [LTerm.degreeAt,LTerm.subterm,Option.bind_some,LTerm.degree,Option.some.injEq] at degree
        cases degree
        exact ⟨_,_,root.walk⟩
  | cons s p ih =>
    cases h with
    | var => cases s <;> simp [LTerm.degreeAt,LTerm.subterm] at degree
    | lam route body =>
      cases s with
      | fn => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | arg => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | body => exact ih body degree
    | app route fn arg =>
      cases s with
      | body => simp [LTerm.degreeAt,LTerm.subterm] at degree
      | fn => exact ih fn degree
      | arg => exact ih arg degree

/-- INIT is fixed at the original source even when the final degree is a new
compound word created after many contractions. -/
theorem History.degree_walk (h : History ps t u) (hi : INIT t) (degree : u.degreeAt p=some alpha) :
    ∃ appId lamId, SourceWalk (sourceEdges [] .external t)
      (.appFn appId) alpha.edgeWord (.lamContext lamId) :=
  (h.generated_source_routes hi).degree_walk degree
end Lamping.Lambda.Labelled
