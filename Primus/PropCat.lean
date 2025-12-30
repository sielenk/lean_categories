import Primus.Category
import Primus.Functor
import Primus.Discrete
import Primus.Two
import Primus.EqualizerDiagram

import Mathlib.Data.Set.Image


def propCat: Cat.{1, 0} := {
  Ob := Prop,
  Hom A B :=  A -> B,
  id _ x := x,
  compose g f x := g (f x)
  left_id _ := rfl
  right_id _ := rfl
  assoc _ _ _ := rfl
}

def propTerminal: TerminalObject propCat := {
  T := True
  hom _ _ := True.intro
  unique _ _ := rfl
}

def propInitial: InitialObject propCat := {
  I := False
  hom X := False.elim
  unique X g := by
    funext x
    exact x.elim
}

theorem propMono{A B: propCat.Ob}(f: propCat.Hom A B): mono f :=
  λ _ _ _ ↦ rfl

theorem propEpi{A B: propCat.Ob}(f: propCat.Hom A B): epi f :=
  λ _ _ _ ↦ rfl

theorem propThin: thin propCat :=
  λ _ _ _ _ ↦ rfl

def PropLimit{JJ: Cat}(F: Fun JJ propCat): Lim F := {
  T := {
    N := ∀j, F.onOb j
    π J H := H J
    comm _ := rfl
  }
  hom X := {
    h n j := X.π j n
    fac _ := rfl
  }
  unique _ _ := rfl
}
