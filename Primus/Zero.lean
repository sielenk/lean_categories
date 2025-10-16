import Primus.Category

def zero: category.{0, 0} := {
  Ob := Empty
  Hom _ _ := Empty
  id A := A
  compose A _ := A
  left_id f := f.elim
  right_id f := f.elim
  assoc _ f _ := f.elim
}
