import Primus.Category


inductive twoOb.{n}: Type n
  | ob1: twoOb
  | ob2: twoOb

inductive twoHom.{m, n}: twoOb.{m} -> twoOb.{m} -> Type n
  | id1: twoHom twoOb.ob1 twoOb.ob1
  | id2: twoHom twoOb.ob2 twoOb.ob2
  | f12: twoHom twoOb.ob1 twoOb.ob2

 def two: category := {
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
    cases h <;> cases g <;> cases f <;> rfl
}
