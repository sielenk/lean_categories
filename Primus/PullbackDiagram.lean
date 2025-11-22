import Primus.Category
import Primus.Functor
import Primus.Lim


inductive pullbackOb: Type
  | A₁: pullbackOb
  | A₂: pullbackOb
  | B: pullbackOb

inductive pullbackHom: pullbackOb -> pullbackOb -> Type
  | idA₁: pullbackHom pullbackOb.A₁ pullbackOb.A₁
  | idA₂: pullbackHom pullbackOb.A₂ pullbackOb.A₂
  | idB: pullbackHom pullbackOb.B pullbackOb.B
  | f₁: pullbackHom pullbackOb.A₁ pullbackOb.B
  | f₂: pullbackHom pullbackOb.A₂ pullbackOb.B

def pullbackId(A: pullbackOb): pullbackHom A A :=
  match A with
  | pullbackOb.A₁ => pullbackHom.idA₁
  | pullbackOb.A₂ => pullbackHom.idA₂
  | pullbackOb.B => pullbackHom.idB

def pullbackComp{X Y Z: pullbackOb}(g: pullbackHom Y Z)(f: pullbackHom X Y): pullbackHom X Z :=
  match f, g with
  | pullbackHom.idA₁, pullbackHom.idA₁ => pullbackHom.idA₁
  | pullbackHom.idA₁, pullbackHom.f₁ => pullbackHom.f₁
  | pullbackHom.idA₂, pullbackHom.f₂ => pullbackHom.f₂
  | pullbackHom.idA₂, pullbackHom.idA₂ => pullbackHom.idA₂
  | pullbackHom.f₁, pullbackHom.idB => pullbackHom.f₁
  | pullbackHom.f₂, pullbackHom.idB => pullbackHom.f₂
  | pullbackHom.idB, pullbackHom.idB => pullbackHom.idB

@[simp] def pullbackId_A₁: pullbackHom.idA₁ = pullbackId pullbackOb.A₁ := rfl
@[simp] def pullbackId_A₂: pullbackHom.idA₂ = pullbackId pullbackOb.A₂ := rfl
@[simp] def pullbackId_B: pullbackHom.idB = pullbackId pullbackOb.B := rfl

@[simp] def pullbackLeftId {X Y: pullbackOb}(f: pullbackHom X Y): pullbackComp (pullbackId Y) f = f := by
  cases f <;> rfl

@[simp] def pullbackRightId {X Y: pullbackOb}(f: pullbackHom X Y): pullbackComp f (pullbackId X) = f := by
  cases f <;> rfl

def pullbackDiagram: category.{1, 1} := {
  Ob := pullbackOb,
  Hom := pullbackHom,
  id := pullbackId,
  compose := pullbackComp,
  left_id := pullbackLeftId,
  right_id := pullbackRightId,
  assoc h g f := by
    cases g <;> cases f <;> simp
}


def pullbackFunctor{CC: category}{A₁ A₂ B: CC.Ob}
    (f₁: CC.Hom A₁ B)(f₂: CC.Hom A₂ B): functor pullbackDiagram CC := {
  onOb A := match A with
    | pullbackOb.A₁ => A₁
    | pullbackOb.A₂ => A₂
    | pullbackOb.B => B,
  onHom f := match f with
    | pullbackHom.idA₁ => CC.id A₁
    | pullbackHom.idA₂ => CC.id A₂
    | pullbackHom.idB => CC.id B
    | pullbackHom.f₁ => f₁
    | pullbackHom.f₂ => f₂
  id{X} := by
    cases X <;> rfl,
  compose{X Y Z g f} := by
    cases g <;> cases f <;> simp <;> rfl
}

def pullback{CC: category}{A₁ A₂ B: CC.Ob}
    (f₁: CC.Hom A₁ B)(f₂: CC.Hom A₂ B) :=
  lim (pullbackFunctor f₁ f₂)
