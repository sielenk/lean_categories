import Primus.Category


def one: category.{0, 0} := {
  Ob := PUnit,
  Hom _ _ := PUnit,
  id _ := Unit.unit,
  compose _ _ := Unit.unit,
  left_id := Eq.refl
  right_id := Eq.refl
  assoc _ _ _ := Eq.refl Unit.unit
}
