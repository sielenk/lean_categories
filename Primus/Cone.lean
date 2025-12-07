import Primus.Category
import Primus.Functor


variable {JJ CC: category}
variable (F: functor JJ CC)

structure coneOb: Sort _ where
  N: CC.Ob
  π J : CC.Hom N (F.onOb J)
  comm{J₁ J₂}(f: JJ.Hom J₁ J₂): CC.compose (F.onHom f) (π J₁) = π J₂

attribute [simp] coneOb.comm

structure coneHom(X Y: coneOb F): Sort _ where
  h: CC.Hom X.N Y.N
  fac J: CC.compose (Y.π J) h = X.π J

attribute [simp] coneHom.fac

def coneCat: category := {
  Ob := coneOb F,
  Hom := coneHom F,
  id X := ⟨CC.id X.N, by
    intro J
    rw [CC.right_id]
  ⟩
  compose{A B C} g f := ⟨CC.compose g.h f.h, by
    intro J
    rw [CC.assoc, g.fac, f.fac]
  ⟩
  left_id {A B} f := by
    simp
  right_id {A B} f := by
    simp
  assoc {A B C D} h g f := by
    simp
    apply CC.assoc
}

@[simp] def coneCatOb: coneOb F = (coneCat F).Ob := rfl
@[simp] def coneCatHom: coneHom F = (coneCat F).Hom := rfl
