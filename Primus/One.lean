import Primus.Category


def one.{m, n}: category.{m, n} := {
  Ob := PUnit.{m},
  Hom _ _ := PUnit.{n},
  id _ := PUnit.unit,
  compose _ _ := PUnit.unit,
  left_id := Eq.refl
  right_id := Eq.refl
  assoc _ _ _ := Eq.refl PUnit.unit
}
