import Primus.Category


inductive discreteHom{X: Type _} : X → X → Type _
| id(A: X): discreteHom A A

def discreteCat(X: Type _): category := {
  Ob := X
  Hom := discreteHom
  id := discreteHom.id
  compose g f :=
    match g, f with
    | discreteHom.id _, discreteHom.id _ => discreteHom.id _
  left_id f :=
    match f with
    | discreteHom.id _ => rfl
  right_id f := by
    match f with
    | discreteHom.id _ => rfl
  assoc h g f := by
    match h, g, f with
    | discreteHom.id _, discreteHom.id _, discreteHom.id _ => rfl
}
