import Primus.Category
import Primus.Functor


variable {AA BB CC: category}
variable (S: functor AA CC)
variable (T: functor BB CC)

structure commaOb: Type _ where
  A: AA.Ob
  B: BB.Ob
  h: CC.Hom (S.onOb A) (T.onOb B)

structure commaHom(X Y: commaOb S T): Type _ where
  f: AA.Hom X.A Y.A
  g: BB.Hom X.B Y.B
  comm: CC.compose Y.h (S.onHom f) = CC.compose (T.onHom g) X.h

def commaCat: category := {
  Ob := commaOb S T,
  Hom := commaHom S T,
  id X := by
    apply commaHom.mk (AA.id X.A) (BB.id X.B)
    rw [S.id, CC.right_id]
    rw [T.id, CC.left_id]
  compose{A B C} g f := by
    apply commaHom.mk (AA.compose g.f f.f) (BB.compose g.g f.g)
    rw [S.compose, CC.assoc, g.comm, T.compose, ← CC.assoc, ← CC.assoc, f.comm]
  left_id {A B} f := by
    simp
  right_id {A B} f := by
    simp
  assoc {A B C D} h g f := by
    simp
    and_intros
    apply AA.assoc
    apply BB.assoc
}
