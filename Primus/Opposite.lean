import Primus.Category


def op(CC: category): category := {
  Ob := CC.Ob,
  Hom A B := CC.Hom B A,
  id A := CC.id A,
  compose g f := CC.compose f g,
  left_id := CC.right_id
  right_id := CC.left_id
  assoc h g f := Eq.symm (CC.assoc f g h)
}
