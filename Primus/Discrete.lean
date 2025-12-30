import Primus.Category


def discreteCat.{n}(X: Sort n): Category.{n, 0} := {
  Ob := X
  Hom := Eq
  id A := rfl
  compose g f := Eq.trans f g
  left_id f := rfl
  right_id f := rfl
  assoc h g f := by
    simp
}
