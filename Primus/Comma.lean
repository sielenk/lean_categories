import Primus.Category

universe m n

variable {AA BB CC: category.{m, n}}
variable (S: functor AA CC)
variable (T: functor BB CC)

structure commaOb: Type max m n where
  A: AA.Ob
  B: BB.Ob
  h: CC.Hom (S.onOb A) (T.onOb B)

structure commaHom(X Y: commaOb S T): Type n where
  f: AA.Hom X.A Y.A
  g: BB.Hom X.B Y.B
  comm: CC.compose Y.h (S.onHom f) = CC.compose (T.onHom g) X.h

def comma: category := {
  Ob := commaOb S T,
  Hom := commaHom S T,
  id X := by
    apply commaHom.mk (AA.id X.A) (BB.id X.B)
    rw [S.id, CC.right_id]
    rw [T.id, CC.left_id]
  compose{A B C} f g := by
    apply commaHom.mk (AA.compose f.f g.f) (BB.compose f.g g.g)
    rw [S.compose, CC.assoc, f.comm, T.compose, ← CC.assoc, ← CC.assoc, g.comm]
  left_id {A B} f := by
    simp
    congr
    apply AA.left_id
    apply BB.left_id
  right_id {A B} f := by
    simp
    congr
    apply AA.right_id
    apply BB.right_id
  assoc {A B C D} f g h := by
    simp
    and_intros
    apply AA.assoc
    apply BB.assoc
}
