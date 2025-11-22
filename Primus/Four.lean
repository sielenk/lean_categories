import Primus.Category


inductive fourOb.{m}: Type m
  | ob1: fourOb
  | ob2: fourOb
  | ob3: fourOb
  | ob4: fourOb

inductive fourHom.{m, n}: fourOb.{m} -> fourOb.{m} -> Type n
  | id1: fourHom fourOb.ob1 fourOb.ob1
  | f12: fourHom fourOb.ob1 fourOb.ob2
  | f13: fourHom fourOb.ob1 fourOb.ob3
  | f14: fourHom fourOb.ob1 fourOb.ob4
  | id2: fourHom fourOb.ob2 fourOb.ob2
  | f23: fourHom fourOb.ob2 fourOb.ob3
  | f24: fourHom fourOb.ob2 fourOb.ob4
  | id3: fourHom fourOb.ob3 fourOb.ob3
  | f34: fourHom fourOb.ob3 fourOb.ob4
  | id4: fourHom fourOb.ob4 fourOb.ob4

def fourId(A: fourOb): fourHom A A :=
  match A with
  | fourOb.ob1 => fourHom.id1
  | fourOb.ob2 => fourHom.id2
  | fourOb.ob3 => fourHom.id3
  | fourOb.ob4 => fourHom.id4

def fourComp{A B C: fourOb}(g: fourHom B C)(f: fourHom A B): fourHom A C :=
  match f, g with
  | fourHom.id1, fourHom.id1 => fourHom.id1
  | fourHom.id1, fourHom.f12 => fourHom.f12
  | fourHom.id1, fourHom.f13 => fourHom.f13
  | fourHom.id1, fourHom.f14 => fourHom.f14
  | fourHom.id2, fourHom.id2 => fourHom.id2
  | fourHom.id2, fourHom.f23 => fourHom.f23
  | fourHom.id2, fourHom.f24 => fourHom.f24
  | fourHom.id3, fourHom.id3 => fourHom.id3
  | fourHom.id3, fourHom.f34 => fourHom.f34
  | fourHom.id4, fourHom.id4 => fourHom.id4
  | fourHom.f12, fourHom.id2 => fourHom.f12
  | fourHom.f12, fourHom.f23 => fourHom.f13
  | fourHom.f12, fourHom.f24 => fourHom.f14
  | fourHom.f13, fourHom.id3 => fourHom.f13
  | fourHom.f13, fourHom.f34 => fourHom.f14
  | fourHom.f14, fourHom.id4 => fourHom.f14
  | fourHom.f23, fourHom.id3 => fourHom.f23
  | fourHom.f23, fourHom.f34 => fourHom.f24
  | fourHom.f24, fourHom.id4 => fourHom.f24
  | fourHom.f34, fourHom.id4 => fourHom.f34

def four.{m, n}: category.{m+1, n+1} := {
  Ob := fourOb.{m}
  Hom := fourHom.{m, n}
  id := fourId
  compose := fourComp
  left_id f := by
    cases f <;> rfl
  right_id f := by
    cases f <;> rfl
  assoc h g f := by
    cases h <;> cases g <;> cases f <;> rfl
}
