import Primus.Category
import Primus.Functor
import Primus.Discrete
import Primus.Two
import Primus.EqualizerDiagram

import Mathlib.Data.Set.Image


def PropCat: category.{1, 0} := {
  Ob := Prop,
  Hom A B :=  A -> B,
  id _ x := x,
  compose g f x := g (f x)
  left_id _ := rfl
  right_id _ := rfl
  assoc _ _ _ := rfl
}

def propTerminal: terminalObject PropCat := {
  T := True
  hom _ := fun _ => True.intro
  unique _ _ := rfl
}

def propInitial: initialObject PropCat := {
  I := False
  hom X := False.elim
  unique X g := by
    funext x
    exact x.elim
}

theorem propMono{A B: PropCat.Ob}(f: PropCat.Hom A B): mono f :=
  λ _ _ _ ↦ rfl

theorem propEpi{A B: PropCat.Ob}(f: PropCat.Hom A B): epi f :=
  λ _ _ _ ↦ rfl

theorem propThin: thin PropCat :=
  λ _ _ _ _ ↦ rfl

def propLimit{JJ: category}(F: functor JJ PropCat): lim F := {
  T := {
    N := ∀j, F.onOb j
    π J := λ H ↦ H J
    comm _ := rfl
  }
  hom X := {
    h := λ n j ↦ X.π j n
    fac _ := rfl
  }
  unique _ _ := rfl
}
