import Primus.Category


def Set.{m}: category.{m+1, m} := {
  Ob := Type m,
  Hom A B :=  A -> B,
  id A x := x,
  compose{A B C} g f := g ∘ f
  left_id{A B} f := by
    rfl
  right_id{A B} f := by
    rfl
  assoc{A B C D} h g f := by
    rfl
}
