import Primus.Category


def one: category := {
  Ob := PUnit,
  Hom _ _ := PUnit,
  id _ := PUnit.unit,
  compose _ _ := PUnit.unit,
  left_id := Eq.refl
  right_id := Eq.refl
  assoc _ _ _ := Eq.refl Unit.unit
}
