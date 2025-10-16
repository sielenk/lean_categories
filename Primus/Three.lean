import Primus.Category

inductive threeOb: Type
  | ob1: threeOb
  | ob2: threeOb
  | ob3: threeOb

inductive threeHom: threeOb -> threeOb -> Type
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

def threeLeftId {A B: threeOb}(f: threeHom A B): threeComp (threeId B) f = f :=
  match f with
  | threeHom.id1 => rfl
  | threeHom.id2 => rfl
  | threeHom.id3 => rfl
  | threeHom.f12 => rfl
  | threeHom.f23 => rfl
  | threeHom.f13 => rfl

def threeRightId {A B: threeOb}(f: threeHom A B): threeComp f (threeId A) = f :=
  match f with
  | threeHom.id1 => rfl
  | threeHom.id2 => rfl
  | threeHom.id3 => rfl
  | threeHom.f12 => rfl
  | threeHom.f23 => rfl
  | threeHom.f13 => rfl

def three: category.{0} := {
  Ob := threeOb,
  Hom := threeHom,
  id := threeId,
  compose{A B C} := threeComp,
  left_id{A B} := threeLeftId,
  right_id{A B} := threeRightId,
  assoc{A B C D} h g f := by
    cases g
    . case id1 =>
      have H1: threeHom.id1 = threeId threeOb.ob1 := rfl
      rw [H1]
      clear H1
      rw [threeLeftId f]
      rw [threeRightId h]
    . case id2 =>
      have H1: threeHom.id2 = threeId threeOb.ob2 := rfl
      rw [H1]
      clear H1
      rw [threeLeftId f]
      rw [threeRightId h]
    . case id3 =>
      have H1: threeHom.id3 = threeId threeOb.ob3 := rfl
      rw [H1]
      clear H1
      rw [threeLeftId f]
      rw [threeRightId h]
    . case f12 =>
      cases f
      have H1: threeHom.id1 = threeId threeOb.ob1 := rfl
      rw [H1]
      clear H1
      rw [threeRightId (threeComp h threeHom.f12)]
      rw [threeRightId threeHom.f12]
    . case f23 =>
      cases h
      have H1: threeHom.id3 = threeId threeOb.ob3 := rfl
      rw [H1]
      clear H1
      rw [threeLeftId (threeComp threeHom.f23 f)]
      rw [threeLeftId threeHom.f23]
    . case f13 =>
      cases f
      cases h
      have H1: threeHom.id1 = threeId threeOb.ob1 := rfl
      rw [H1]
      clear H1
      have H1: threeHom.id3 = threeId threeOb.ob3 := rfl
      rw [H1]
      clear H1
      rw [threeRightId threeHom.f13]
      rw [threeLeftId threeHom.f13]
      rw [threeRightId threeHom.f13]
}
