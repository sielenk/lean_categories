import Primus.Category
import Primus.Functor
import Primus.Lim


inductive equalizerOb: Type
  | A: equalizerOb
  | B: equalizerOb

inductive equalizerHom: equalizerOb -> equalizerOb -> Type
  | idA: equalizerHom equalizerOb.A equalizerOb.A
  | idB: equalizerHom equalizerOb.B equalizerOb.B
  | f₁: equalizerHom equalizerOb.A equalizerOb.B
  | f₂: equalizerHom equalizerOb.A equalizerOb.B

 def equalizerDiagram: category := {
  Ob := equalizerOb
  Hom := equalizerHom
  id X := match X with
    | equalizerOb.A => equalizerHom.idA
    | equalizerOb.B => equalizerHom.idB
  compose g f := match f, g with
    | equalizerHom.idA, equalizerHom.idA => equalizerHom.idA
    | equalizerHom.idB, equalizerHom.idB => equalizerHom.idB
    | equalizerHom.f₁, equalizerHom.idB => equalizerHom.f₁
    | equalizerHom.f₂, equalizerHom.idB => equalizerHom.f₂
    | equalizerHom.idA, equalizerHom.f₁ => equalizerHom.f₁
    | equalizerHom.idA, equalizerHom.f₂ => equalizerHom.f₂
  left_id f := by
    cases f <;>  rfl
  right_id f:= by
    cases f <;>  rfl
  assoc h g f := by
    cases h <;> cases g <;> cases f <;> rfl
}

def equalizerFunctor{CC: category}{A B: CC.Ob}
    (f₁: CC.Hom A B)(f₂: CC.Hom A B): functor equalizerDiagram CC := {
  onOb X := match X with
    | equalizerOb.A => A
    | equalizerOb.B => B,
  onHom f := match f with
    | equalizerHom.idA => CC.id A
    | equalizerHom.idB => CC.id B
    | equalizerHom.f₁ => f₁
    | equalizerHom.f₂ => f₂
  id{X} := by
    cases X <;> rfl,
  compose{X Y Z g f} := by
    cases g <;> cases f <;> simp <;> rfl
}

def equalizer{CC: category}{A B: CC.Ob}
    (f₁: CC.Hom A B)(f₂: CC.Hom A B) :=
  lim (equalizerFunctor f₁ f₂)
