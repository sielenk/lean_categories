import Primus.Category
import Primus.Functor


variable {JJ CC: Cat}
variable (F: Fun JJ CC)

structure ConeOb: Sort _ where
  N: CC.Ob
  π J : CC.Hom N (F.onOb J)
  comm{J₁ J₂}(f: JJ.Hom J₁ J₂): CC.compose (F.onHom f) (π J₁) = π J₂

attribute [simp] ConeOb.comm

@[ext]
theorem ConeOb.ext{X₁ X₂: ConeOb F}:
  X₁.N = X₂.N -> X₁.π ≍ X₂.π -> X₁ = X₂
:= by
  let ⟨N, π₁, H₁⟩ := X₁
  let ⟨N', π₂, H₂⟩ := X₂
  simp
  intro HN Hπ
  subst HN
  and_intros; rfl
  assumption


structure ConeHom(X Y: ConeOb F): Sort _ where
  h: CC.Hom X.N Y.N
  fac J: CC.compose (Y.π J) h = X.π J

attribute [simp] ConeHom.fac

@[ext]
theorem ConeHom.ext{X Y}{f₁ f₂: ConeHom F X Y}:
  f₁.h = f₂.h -> f₁ = f₂
:= by
  cases f₁; cases f₂; simp

def coneCat: Cat := {
  Ob := ConeOb F,
  Hom := ConeHom F,
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

@[simp] def coneCatOb: ConeOb F = (coneCat F).Ob := rfl
@[simp] def coneCatHom: ConeHom F = (coneCat F).Hom := rfl
