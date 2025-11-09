import Primus.Category
import Primus.Opposite
import Primus.Functor
import Primus.SortCat


def homFun.{m, n}{CC: category.{m, n}}(X: CC.Ob):
  functor (op CC) SortCat.{n} :=
{
  onOb := (op CC).Hom X,
  onHom := (op CC).compose,
  id{A} := by
    funext h
    unfold SortCat; simp,
  compose{A B C g f} := by
    funext h
    unfold SortCat; simp
    rw [(op CC).assoc]
}
