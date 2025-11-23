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

def yoneda_embedding(CC: category):
  functor CC (FunctorCat (op CC) SortCat)
:= {
  onOb := homFun
  onHom {C D} h := {
    η C := CC.compose h
    naturality := by
      simp [SortCat, op, homFun]
      intro B A f
      funext g
      apply CC.assoc
  }
  id := by
    simp [FunctorCat, SortCat, homFun, natTransId, op]
    intro A
    funext B f
    simp
  compose := by
    simp [FunctorCat, SortCat, homFun, natTransComp, op]
    intro B C D h g
    funext A f
    rw [CC.assoc]
}

theorem yoneda_fully_faithful(CC: category):
  fullyFaithful (yoneda_embedding CC)
:= by
  split_ands
  . intro X Y nt
    use nt.η X (CC.id X)
    simp [yoneda_embedding]
    congr
    funext Z f
    have H1 := @nt.naturality X Z f
    simp [FunctorCat, yoneda_embedding, homFun, op, SortCat] at H1
    let g := λ x ↦ CC.compose (nt.η X x) f
    change _ = g at H1
    trans  g (CC.id X)
    rfl
    rw [←H1]
    simp
  . intro X Y f1 f2 H1
    let ye := yoneda_embedding CC
    let nt₁ := (ye.onHom f1)
    let nt₂ := (ye.onHom f2)
    change nt₁ = nt₂ at H1
    have H2: nt₁.η X (CC.id X) = nt₂.η X (CC.id X) := by rw [H1]
    simp [nt₁, nt₂, ye, yoneda_embedding] at H2
    assumption
