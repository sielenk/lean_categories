import Primus.Category
import Primus.Functor


structure naturalTransformation{CC DD: Category}(F G: functor CC DD): Sort _ where
  η: (A: CC.Ob) -> DD.Hom (F.onOb A) (G.onOb A)
  naturality{A B: CC.Ob}(f: CC.Hom A B): DD.compose (η B) (F.onHom f) = DD.compose (G.onHom f) (η A)

def natTransId{CC DD: Category}(F: functor CC DD): naturalTransformation F F := {
  η A := DD.id (F.onOb A),
  naturality{A B} f := by
    rw [DD.left_id, DD.right_id]
}

def natTransComp{CC DD: Category}{F G H: functor CC DD}
  (ntG: naturalTransformation G H)
  (ntF: naturalTransformation F G): naturalTransformation F H := {
  η A := DD.compose (ntG.η A) (ntF.η A),
  naturality{A B} f := by
    rw [DD.assoc, ←ntG.naturality f, ←DD.assoc, ntF.naturality f, DD.assoc]
  }

def FunctorCat(CC DD: Category): Category := {
  Ob := functor CC DD,
  Hom := naturalTransformation,
  id := natTransId,
  compose := natTransComp,
  left_id {A B} f := by
    unfold natTransComp natTransId
    cases f
    simp
  right_id {A B} f := by
    unfold natTransComp natTransId
    cases f
    simp
  assoc {A B C D} h g f := by
    unfold natTransComp
    cases h
    cases g
    cases f
    simp
    funext
    rw [DD.assoc]
}
