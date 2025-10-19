import Primus.Category
import Primus.Functor


structure naturalTransformation{CC DD: category}(F G: functor CC DD): Type _ where
  eta: (A: CC.Ob) -> DD.Hom (F.onOb A) (G.onOb A)
  naturality{A B: CC.Ob}(f: CC.Hom A B): DD.compose (eta B) (F.onHom f) = DD.compose (G.onHom f) (eta A)

def natTransId{CC DD: category}(F: functor CC DD): naturalTransformation F F := {
  eta A := DD.id (F.onOb A),
  naturality{A B} f := by
    rw [DD.left_id, DD.right_id]
}

def natTransComp{CC DD: category}{F G H: functor CC DD}
  (ntG: naturalTransformation G H)
  (ntF: naturalTransformation F G): naturalTransformation F H := {
  eta A := DD.compose (ntG.eta A) (ntF.eta A),
  naturality{A B} f := by
    rw [DD.assoc, ←ntG.naturality f, ←DD.assoc, ntF.naturality f, DD.assoc]
  }

def FunctorCat(CC DD: category): category := {
  Ob := functor CC DD,
  Hom := naturalTransformation,
  id := natTransId,
  compose := natTransComp,
  left_id {A B} f := by
    unfold natTransComp natTransId
    cases f
    simp
    funext
    rw [DD.left_id]
  right_id {A B} f := by
    unfold natTransComp natTransId
    cases f
    simp
    funext
    rw [DD.right_id]
  assoc {A B C D} h g f := by
    unfold natTransComp
    cases h
    cases g
    cases f
    simp
    funext
    rw [DD.assoc]
}
