import Primus.Category
import Primus.Functor


variable {JJ CC: Cat}


@[ext]
structure CoConeOb(F: Fun JJ CC): Sort _ where
  N: CC.Ob
  π J : CC.Hom (F.onOb J) N
  comm{J₁ J₂}(f: JJ.Hom J₁ J₂): CC.compose (π J₂) (F.onHom f) = π J₁

attribute [simp] CoConeOb.comm


@[ext]
structure CoConeHom{F}(X Y: @CoConeOb JJ CC F): Sort _ where
  h: CC.Hom X.N Y.N
  fac J: CC.compose h (X.π J) = Y.π J

attribute [simp] CoConeHom.fac


def coConeCat(F: Fun JJ CC): Cat := {
  Ob := CoConeOb F,
  Hom := CoConeHom,
  id X := ⟨CC.id X.N, by
    intro J
    rw [CC.left_id]
  ⟩
  compose g f := ⟨CC.compose g.h f.h, by
    intro J
    rw [←CC.assoc, f.fac, g.fac]
  ⟩
  left_id f := by
    simp
  right_id f := by
    simp
  assoc h g f := by
    simp
    rw [CC.assoc]
}

@[simp] def coConeCatOb {F: Fun JJ CC}: CoConeOb F = (coConeCat F).Ob  := rfl
@[simp] def coConeCatHom{F: Fun JJ CC}: CoConeHom  = (coConeCat F).Hom := rfl
