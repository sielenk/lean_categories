import Primus.Category


structure functor(CC DD: category) : Sort _ where
  onOb: CC.Ob -> DD.Ob
  onHom{A B: CC.Ob}: CC.Hom A B -> DD.Hom (onOb A) (onOb B)
  id{A: CC.Ob}: onHom (CC.id A) = DD.id (onOb A)
  compose{A B C: CC.Ob}{g: CC.Hom B C}{f: CC.Hom A B}:
         onHom (CC.compose g f) = DD.compose (onHom g) (onHom f)

def functorId(CC: category): functor CC CC := {
  onOb A := A,
  onHom{_ _} f:= f,
  id{A} := Eq.refl (CC.id A),
  compose{_ _ _ g f} := Eq.refl (CC.compose g f)
}

def functorComp{AA BB CC}(G: functor BB CC)(F: functor AA BB): functor AA CC := {
  onOb A := G.onOb (F.onOb A),
  onHom f := G.onHom (F.onHom f),
  id{A} := by
    rw [F.id, G.id],
  compose{A B C g f} := by
    rw [F.compose, G.compose]
}

def CategoryCat : category := {
  Ob := category,
  Hom := functor,
  id := functorId,
  compose := functorComp,
  left_id _ := by funext; rfl,
  right_id _ := by funext; rfl,
  assoc _ _ _ := by funext; rfl
}
