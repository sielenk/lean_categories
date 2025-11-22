import Primus.Category


inductive threeOb.{m}: Type m
  | ob1: threeOb
  | ob2: threeOb
  | ob3: threeOb

inductive threeHom.{m, n}: threeOb.{m} -> threeOb.{m} -> Type n
  | id1: threeHom threeOb.ob1 threeOb.ob1
  | id2: threeHom threeOb.ob2 threeOb.ob2
  | id3: threeHom threeOb.ob3 threeOb.ob3
  | f12: threeHom threeOb.ob1 threeOb.ob2
  | f23: threeHom threeOb.ob2 threeOb.ob3
  | f13: threeHom threeOb.ob1 threeOb.ob3

def threeId(A: threeOb): threeHom A A :=
  match A with
  | threeOb.ob1 => threeHom.id1
  | threeOb.ob2 => threeHom.id2
  | threeOb.ob3 => threeHom.id3

def threeComp{A B C: threeOb}(g: threeHom B C)(f: threeHom A B): threeHom A C :=
  match f, g with
  | threeHom.id1, threeHom.id1 => threeHom.id1
  | threeHom.id1, threeHom.f12 => threeHom.f12
  | threeHom.id1, threeHom.f13 => threeHom.f13
  | threeHom.id2, threeHom.id2 => threeHom.id2
  | threeHom.id2, threeHom.f23 => threeHom.f23
  | threeHom.id3, threeHom.id3 => threeHom.id3
  | threeHom.f12, threeHom.id2 => threeHom.f12
  | threeHom.f12, threeHom.f23 => threeHom.f13
  | threeHom.f13, threeHom.id3 => threeHom.f13
  | threeHom.f23, threeHom.id3 => threeHom.f23

@[simp] def three_id1: threeHom.id1 = threeId threeOb.ob1 := rfl
@[simp] def three_id2: threeHom.id2 = threeId threeOb.ob2 := rfl
@[simp] def three_id3: threeHom.id3 = threeId threeOb.ob3 := rfl

@[simp] def threeLeftId {A B: threeOb}(f: threeHom A B): threeComp (threeId B) f = f := by
  cases f <;> rfl

@[simp] def threeRightId {A B: threeOb}(f: threeHom A B): threeComp f (threeId A) = f := by
  cases f <;> rfl

def three.{m, n}: category.{m+1, n+1} := {
  Ob := threeOb.{m},
  Hom := threeHom.{m, n},
  id := threeId,
  compose{A B C} := threeComp,
  left_id{A B} := threeLeftId,
  right_id{A B} := threeRightId,
  assoc{A B C D} h g f := by
    cases g <;> try simp
    . case f12 =>
      cases f <;> simp
    . case f23 =>
      cases h <;> simp
    . case f13 =>
      cases f <;> cases h <;> simp
}
