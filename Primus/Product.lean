import Primus.Category


def prodCat(CC DD: category): category := {
  Ob := CC.Ob × DD.Ob,
  Hom X Y := CC.Hom X.1 Y.1 × DD.Hom X.2 Y.2,
  id X := (CC.id X.1, DD.id X.2),
  compose{X Y Z} g f:= (CC.compose g.1 f.1, DD.compose g.2 f.2),
  left_id{A B} f := by
    cases f
    simp
    and_intros
    apply CC.left_id
    apply DD.left_id
  right_id{A B} f := by
    cases f
    simp
    and_intros
    apply CC.right_id
    apply DD.right_id
  assoc{A B C D} h g f:= by
    cases h
    cases g
    cases f
    simp
    and_intros
    apply CC.assoc
    apply DD.assoc
}
