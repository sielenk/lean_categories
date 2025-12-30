import Primus.Category
import Primus.Opposite
import Primus.Functor
import Primus.NatTrans
import Primus.SortCat


def homFun.{m, n}{CC: Cat.{m, n}}(X: CC.Ob): Fun (op CC) sortCat.{n} := {
  onOb := (op CC).Hom X,
  onHom := (op CC).compose,
  id{A} := by
    funext h
    simp [sortCat, op]
  compose{A B C g f} := by
    funext h
    simp [sortCat, op]
    rw [CC.assoc]
}


def yonedaDown{CC: Cat}(F: Fun (op CC) sortCat)(X: CC.Ob):
  sortCat.Hom (NaturalTransformation (homFun X) F) (F.onOb X)
:=
  fun nt => nt.η X (CC.id X)

def yonedaUp{CC: Cat}(F: Fun (op CC) sortCat)(X: CC.Ob):
  sortCat.Hom (F.onOb X) (NaturalTransformation (homFun X) F)
:=
  fun x => {
    η Y f := F.onHom f x,
    naturality{A B} f := by
      funext g
      simp [sortCat, homFun, op, Fun.compose]
  }

theorem yoneda{CC: Cat}(F: Fun (op CC) sortCat)(X: CC.Ob):
  isomorphic (NaturalTransformation (homFun X) F) (F.onOb X)
:= by
  use yonedaDown F X, yonedaUp F X
  simp [sortCat, yonedaDown, yonedaUp]
  split_ands
  · funext ⟨η, H1⟩; simp [op, homFun] at η H1
    congr
    funext Y f; simp
    trans (λ x ↦ η Y (CC.compose x f)) (CC.id X)
    rw [H1 f]
    simp
  · apply F.id

def yonedaEmbedding(CC: Cat):
  Fun CC (functorCat (op CC) sortCat)
:= {
  onOb := homFun
  onHom {C D} h := {
    η C := CC.compose h
    naturality := by
      simp [sortCat, op, homFun]
      intro B A f
      funext g
      apply CC.assoc
  }
  id := by
    simp [functorCat, sortCat, homFun, natTransId, op]
    intro A
    funext B f
    simp
  compose := by
    simp [functorCat, sortCat, homFun, natTransComp, op]
    intro B C D h g
    funext A f
    rw [CC.assoc]
}

theorem yonedaFullyFaithful(CC: Cat):
  fullyFaithful (yonedaEmbedding CC)
:= by
  split_ands
  · intro X Y nt
    use nt.η X (CC.id X)
    simp [yonedaEmbedding]
    congr
    funext Z f
    have H1 := @nt.naturality X Z f
    simp [functorCat, yonedaEmbedding, homFun, op, sortCat] at H1
    let g := λ x ↦ CC.compose (nt.η X x) f
    change _ = g at H1
    trans  g (CC.id X)
    · rfl
    · rw [←H1]
      simp
  · intro X Y f1 f2 H1
    let ye := yonedaEmbedding CC
    let nt₁ := (ye.onHom f1)
    let nt₂ := (ye.onHom f2)
    change nt₁ = nt₂ at H1
    have H2: nt₁.η X (CC.id X) = nt₂.η X (CC.id X) := by rw [H1]
    simp [nt₁, nt₂, ye, yonedaEmbedding] at H2
    assumption
