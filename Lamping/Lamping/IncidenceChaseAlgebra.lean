import Lamping.Lamping.ChainIncidenceWalk

namespace Lamping.Lambda.Labelled
open SyntaxIncidence

theorem SyntaxIncidence.Target.valid_edge (actual : Target t e v) :
    (subtermAt t.erase e).isSome := by
  cases v with
  | none => exact False.elim actual
  | some vertex =>
    rcases actual with equal | ⟨stamp,index,origin,body,tail,lookup,_⟩
    · rw [equal]
      rcases vertex.property with ⟨stamp,fn,arg,lookup⟩ | ⟨stamp,body,lookup⟩ <;>
        rw [←LTerm.erase_subterm,lookup] <;> rfl
    · rw [←LTerm.erase_subterm,lookup]; rfl

theorem IncidenceChase.valid_edges (chase : IncidenceChase t v es ds w) :
    ∀ e ∈ es, (subtermAt t.erase e).isSome := by
  induction chase with
  | nil => simp
  | forward source target rest ih =>
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact target.valid_edge
    · exact ih e member
  | backward target source rest ih =>
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact target.valid_edge
    · exact ih e member

theorem IncidenceChase.length (chase : IncidenceChase t v es ds w) :
    es.length=ds.length := by induction chase <;> simp_all

theorem IncidenceChase.append (first : IncidenceChase t v es ds w)
    (second : IncidenceChase t w fs bs z) :
    IncidenceChase t v (es++fs) (ds++bs) z := by
  induction first with
  | nil => exact second
  | forward source target rest ih => exact .forward source target (ih second)
  | backward target source rest ih => exact .backward target source (ih second)

theorem IncidenceChase.reverse (chase : IncidenceChase t v es ds w) :
    IncidenceChase t w es.reverse (ds.reverse.map Bool.not) v := by
  induction chase with
  | nil => exact .nil
  | forward source target rest ih =>
    simpa only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,Bool.not_true]
      using ih.append (.backward target source .nil)
  | backward target source rest ih =>
    simpa only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,Bool.not_false]
      using ih.append (.forward source target .nil)

/-- Each repeated slot retains its literal occurrence; membership is proof only. -/
def IncidenceChase.edgePosition (chase : IncidenceChase t v es ds w)
    (e : Path) (member : e ∈ es) : Position t.erase :=
  ⟨e,chase.valid_edges e member⟩

#print axioms SyntaxIncidence.Target.valid_edge
#print axioms IncidenceChase.valid_edges
#print axioms IncidenceChase.length
#print axioms IncidenceChase.append
#print axioms IncidenceChase.reverse
end Lamping.Lambda.Labelled
