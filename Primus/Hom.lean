import Primus.Category
import Primus.Opposite
import Primus.Functor
import Primus.NatTrans
import Primus.SortCat


def homFun.{m, n}{CC: category.{m, n}}(X: CC.Ob):
  functor (op CC) SortCat.{n}
:= {
  onOb := (op CC).Hom X,
  onHom := (op CC).compose,
  id{A} := by
    funext h
    simp [SortCat, op]
  compose{A B C g f} := by
    funext h
    simp [SortCat, op]
    rw [CC.assoc]
}


def yoneda_down{CC: category}(F: functor (op CC) SortCat)(X: CC.Ob):
  SortCat.Hom (naturalTransformation (homFun X) F) (F.onOb X)
:=
  fun nt => nt.η X (CC.id X)

def yoneda_up{CC: category}(F: functor (op CC) SortCat)(X: CC.Ob):
  SortCat.Hom (F.onOb X) (naturalTransformation (homFun X) F)
:=
  fun x => {
    η Y f := F.onHom f x,
    naturality{A B} f := by
      funext g
      simp [SortCat, homFun, op, functor.compose]
  }

theorem yoneda{CC: category}(F: functor (op CC) SortCat)(X: CC.Ob):
  isomorphic (naturalTransformation (homFun X) F) (F.onOb X)
:= by
  use yoneda_down F X, yoneda_up F X
  simp [SortCat, yoneda_down, yoneda_up]
  split_ands
  . funext ⟨η, H1⟩; simp [op, homFun] at η H1
    congr
    funext Y f; simp
    trans (λ x ↦ η Y (CC.compose x f)) (CC.id X)
    rw [H1 f]
    simp
  . apply F.id
