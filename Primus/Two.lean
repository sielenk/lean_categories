import Primus.Category

inductive twoOb: Type
  | ob1: twoOb
  | ob2: twoOb

inductive twoHom: twoOb -> twoOb -> Type
  | id1: twoHom twoOb.ob1 twoOb.ob1
  | id2: twoHom twoOb.ob2 twoOb.ob2
  | f12: twoHom twoOb.ob1 twoOb.ob2

 def two: category.{0, 0} := {
  Ob := twoOb
  Hom := twoHom
  id A := match A with
    | twoOb.ob1 => twoHom.id1
    | twoOb.ob2 => twoHom.id2
  compose {A B C} g f := match f, g with
    | twoHom.id1, twoHom.id1 => twoHom.id1
    | twoHom.id2, twoHom.id2 => twoHom.id2
    | twoHom.f12, twoHom.id2 => twoHom.f12
    | twoHom.id1, twoHom.f12 => twoHom.f12
  left_id {A B} f := by
    cases f <;>  rfl
  right_id {A B} f:= by
    cases f <;>  rfl
  assoc {A B C D} h g f := by
    cases g
    . case id1 =>
      cases f
      cases h
      rfl
      rfl
    . case id2 =>
      cases h
      cases f
      rfl
      rfl
    . case f12 =>
      cases f
      cases h
      rfl
}
