import Lamping.Lambda.ExtractionContextReflect
namespace Lamping.Lambda.SyntaxContext

def compose : SyntaxContext → SyntaxContext → SyntaxContext
  | .hole,D => D
  | .frame C inner,D => .frame C (inner.compose D)

theorem compose_path (C D : SyntaxContext) : (C.compose D).path=C.path++D.path := by
  induction C with
  | hole => rfl
  | frame outer inner ih => simp only [compose,path,ih,List.cons_append]

theorem compose_plug (C D : SyntaxContext) (t : Term) :
    (C.compose D).plug t=C.plug (D.plug t) := by
  induction C with
  | hole => rfl
  | frame outer inner ih => simp only [compose,plug,ih]

end Lamping.Lambda.SyntaxContext
