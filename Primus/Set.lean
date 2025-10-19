import Primus.Category


def SetCat.{m}: category.{m+1, m} := {
  Ob := Sort m,
  Hom A B :=  A -> B,
  id _ := fun x => x,
  compose g f := g ∘ f
  left_id _ := rfl
  right_id _ := rfl
  assoc _ _ _ := rfl
}
