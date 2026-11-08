import Lamping.Lamping.InitialReadingSignedGraphWalk
import Lamping.Lamping.InitialMatching

namespace Lamping.Checks.InitialReadingSignedGraphWalk
open AG Graph Lambda Lambda.Labelled

private def ii : LTerm := initLabels (.app (.lam (.var 0)) (.lam (.var 0)))
private theorem ii_closed : Closed ii.erase := ⟨Nat.zero_lt_succ 0,Nat.zero_lt_succ 0⟩
private theorem ii_reading : PrerequisiteReading ii [.arg] [[.arg],[.fn]] [false,true] :=
  .lam (parent:=[]) (step:=.arg) rfl (by decide) (.redex_app rfl)

/-- The selector comes from actual closed INIT encoding. The NEW theorem
supplies the very same two physical blocks and their signed source walk. -/
theorem actual_ii_mixed_sign_reading (level : Nat) :
    ∃ selection : OccurrenceFragmentSelection ii (encode level ii.erase).net (.inl ()),
      ∃ positions : List (Position ii.erase),
        positions.map (fun position => position.val)=[[.arg],[.fn]] ∧
        canonicalChainImage selection ii_reading.chain=
          positions.map (fun position => (selection position).fragment.segments) ∧
        orientedChainImage selection ii_reading=
          List.zipWith (fun position forward => (selection position).read forward)
            positions [false,true] ∧
        ∃ last : SourcePort,
          GraphWalk (sourceEdges [] .external ii) (.lamContext (Label.atom 3))
            [⟨3,true⟩,⟨1,false⟩] last := by
  obtain ⟨selection⟩ := (encode_closed_matches ii.erase ii_closed level).occurrence_fragment_selection ii_closed
  obtain ⟨positions,values,canonical,oriented,first,a,b,target,kind,walk⟩ :=
    initial_reading_signed_graph_walk (init_is_INIT _) ii_reading selection
  have start : a=.lamContext (Label.atom 3) := by
    let here : SyntaxIncidence.ProperPosition ii :=
      ⟨[.arg],Or.inr ⟨Label.atom 3,.var (Label.atom 4) 0,rfl⟩⟩
    have same := Option.some.inj (SyntaxIncidence.Target.unique target
      (show SyntaxIncidence.Target ii [.arg] (some here) from Or.inl rfl))
    subst first
    rcases kind with ⟨stamp,fn,arg,lookup,port⟩ | ⟨stamp,body,lookup,port⟩
    · change some (LTerm.lam (Label.atom 3) (.var (Label.atom 4) 0))=some (LTerm.app stamp fn arg) at lookup
      cases lookup
    · change some (LTerm.lam (Label.atom 3) (.var (Label.atom 4) 0))=some (LTerm.lam stamp body) at lookup
      have stamps := (LTerm.lam.inj (Option.some.inj lookup)).1
      exact port.trans (congrArg SourcePort.lamContext stamps.symm)
  have signed :
      (List.zipWith (fun position forward =>
        if forward then (selection position).term.label.edgeWord
        else EdgeWord.reverse (selection position).term.label.edgeWord)
          positions [false,true]).flatten=[⟨3,true⟩,⟨1,false⟩] := by
    cases positions with
    | nil => simp at values
    | cons x rest =>
      cases rest with
      | nil => simp at values
      | cons y tail =>
        have pieces := List.cons.inj values
        have second := List.cons.inj pieces.2
        have empty : tail=[] := List.map_eq_nil_iff.mp second.2
        subst tail
        have px : x.val=[.arg] := pieces.1
        have py : y.val=[.fn] := second.1
        have lx : ii.subterm x.val=some (.lam (Label.atom 3) (.var (Label.atom 4) 0)) := by rw [px];rfl
        have ly : ii.subterm y.val=some (.lam (Label.atom 1) (.var (Label.atom 2) 0)) := by rw [py];rfl
        have sx := Option.some.inj ((selection x).occurrence.lookup.symm.trans lx)
        have sy := Option.some.inj ((selection y).occurrence.lookup.symm.trans ly)
        change (EdgeWord.reverse (selection x).term.label.edgeWord ++
          ((selection y).term.label.edgeWord ++ []))=[⟨3,true⟩,⟨1,false⟩]
        rw [sx,sy]
        rfl
  refine ⟨selection,positions,values,canonical,oriented,b,?_⟩
  rw [start,signed] at walk
  exact walk

#print axioms actual_ii_mixed_sign_reading
end Lamping.Checks.InitialReadingSignedGraphWalk
