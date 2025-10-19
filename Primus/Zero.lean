import Primus.Category


def zero: category := {
  Ob := PEmpty
  Hom _ _ := PEmpty
  id A := A
  compose _ f := f
  left_id f := f.elim
  right_id f := f.elim
  assoc _ g _ := g.elim
}
