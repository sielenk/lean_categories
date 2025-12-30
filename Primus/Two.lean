import Primus.Category


inductive TwoOb.{m}: Type m
  | ob1: TwoOb
  | ob2: TwoOb

inductive TwoHom.{m, n}: TwoOb.{m} -> TwoOb.{m} -> Type n
  | id1: TwoHom TwoOb.ob1 TwoOb.ob1
  | id2: TwoHom TwoOb.ob2 TwoOb.ob2
  | f12: TwoHom TwoOb.ob1 TwoOb.ob2

 def two.{m, n}: Cat.{m+1, n+1} := {
  Ob := TwoOb.{m}
  Hom := TwoHom.{m, n}
  id A := match A with
    | TwoOb.ob1 => TwoHom.id1
    | TwoOb.ob2 => TwoHom.id2
  compose {A B C} g f := match f, g with
    | TwoHom.id1, TwoHom.id1 => TwoHom.id1
    | TwoHom.id2, TwoHom.id2 => TwoHom.id2
    | TwoHom.f12, TwoHom.id2 => TwoHom.f12
    | TwoHom.id1, TwoHom.f12 => TwoHom.f12
  left_id {A B} f := by
    cases f <;>  rfl
  right_id {A B} f:= by
    cases f <;>  rfl
  assoc {A B C D} h g f := by
    cases h <;> cases g <;> cases f <;> rfl
}
