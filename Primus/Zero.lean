import Primus.Category


def zero.{m, n}: category.{m, n} := {
  Ob := PEmpty
  Hom _ _ := PEmpty
  id A := A.elim
  compose _ f := f
  left_id f := f.elim
  right_id f := f.elim
  assoc _ g _ := g.elim
}
