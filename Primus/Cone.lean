import Primus.Category
import Primus.Functor


variable {JJ CC: category}
variable (F: functor JJ CC)

structure coneOb: Type _ where
  N: CC.Ob
  π J : CC.Hom N (F.onOb J)

structure coneHom(X Y: coneOb F): Type _ where
  h: CC.Hom X.N Y.N
  comm: ∀ J: JJ.Ob, X.π J = CC.compose (Y.π J) h

def coneCat: category := {
  Ob := coneOb F,
  Hom := coneHom F,
  id X := by
    apply coneHom.mk (CC.id X.N)
    intro J
    rw [CC.right_id]
  compose{A B C} g f := by
    apply coneHom.mk (CC.compose g.h f.h)
    intro J
    rw [CC.assoc, ←g.comm, ←f.comm]
  left_id {A B} f := by
    simp
    congr
    apply CC.left_id
  right_id {A B} f := by
    simp
    congr
    apply CC.right_id
  assoc {A B C D} h g f := by
    simp
    apply CC.assoc
}
