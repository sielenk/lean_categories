import Primus.Category
import Primus.Functor


variable {JJ CC: category}
variable (F: functor JJ CC)

structure coneOb: Sort _ where
  N: CC.Ob
  π J : CC.Hom N (F.onOb J)

structure coneHom(X Y: coneOb F): Sort _ where
  h: CC.Hom X.N Y.N
  comm J: X.π J = CC.compose (Y.π J) h

def coneCat: category := {
  Ob := coneOb F,
  Hom := coneHom F,
  id X := ⟨CC.id X.N, by
    intro J
    rw [CC.right_id]
  ⟩
  compose{A B C} g f := ⟨CC.compose g.h f.h, by
    intro J
    rw [CC.assoc, ←g.comm, ←f.comm]
  ⟩
  left_id {A B} f := by
    simp
  right_id {A B} f := by
    simp
  assoc {A B C D} h g f := by
    simp
    apply CC.assoc
}
