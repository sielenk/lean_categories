import Primus.Category
import Primus.Functor


variable {AA BB CC: Cat}
variable (S: Fun AA CC)
variable (T: Fun BB CC)

structure CommaOb: Sort _ where
  A: AA.Ob
  B: BB.Ob
  h: CC.Hom (S.onOb A) (T.onOb B)

structure CommaHom(X Y: CommaOb S T): Sort _ where
  f: AA.Hom X.A Y.A
  g: BB.Hom X.B Y.B
  comm: CC.compose Y.h (S.onHom f) = CC.compose (T.onHom g) X.h

def commaCat: Cat := {
  Ob := CommaOb S T,
  Hom := CommaHom S T,
  id X := ⟨AA.id X.A, BB.id X.B, by
    rw [S.id, T.id]
    simp
  ⟩
  compose{A B C} g f := ⟨AA.compose g.f f.f, BB.compose g.g f.g, by
    rw [S.compose, CC.assoc, g.comm, T.compose, ← CC.assoc, ← CC.assoc, f.comm]
  ⟩
  left_id {A B} f := by
    simp
  right_id {A B} f := by
    simp
  assoc {A B C D} h g f := by
    simp
    and_intros
    apply AA.assoc
    apply BB.assoc
}
