import Primus.Core.Category
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Sets


inductive TwoOb.{m}: Type m
  | ob1: TwoOb
  | ob2: TwoOb
deriving DecidableEq, Inhabited

instance : Fintype TwoOb where
  elems := { TwoOb.ob1, TwoOb.ob2 }
  complete X := by cases X <;> simp

inductive TwoHom.{m, n}: TwoOb.{m} -> TwoOb.{m} -> Type n
  | id1: TwoHom TwoOb.ob1 TwoOb.ob1
  | id2: TwoHom TwoOb.ob2 TwoOb.ob2
  | f12: TwoHom TwoOb.ob1 TwoOb.ob2
deriving DecidableEq

instance {A B : TwoOb} : Fintype (TwoHom A B) where
  elems := match A, B with
    | .ob1, .ob1 => { TwoHom.id1 }
    | .ob2, .ob2 => { TwoHom.id2 }
    | .ob1, .ob2 => { TwoHom.f12 }
    | .ob2, .ob1 => ∅
  complete x := by cases x <;> simp

def two.{m, n}: Cat.{m+1, n+1} := {
  Ob := TwoOb.{m}
  Hom := TwoHom.{m, n}
  id A := match A with
    | TwoOb.ob1 => TwoHom.id1
    | TwoOb.ob2 => TwoHom.id2
  compose g f := match f, g with
    | TwoHom.id1, TwoHom.id1 => TwoHom.id1
    | TwoHom.id2, TwoHom.id2 => TwoHom.id2
    | TwoHom.f12, TwoHom.id2 => TwoHom.f12
    | TwoHom.id1, TwoHom.f12 => TwoHom.f12
  left_id f := by
    cases f <;>  rfl
  right_id f:= by
    cases f <;>  rfl
  assoc h g f := by
    cases h <;> cases g <;> cases f <;> rfl
}
