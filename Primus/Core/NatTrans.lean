import Primus.Core.Category
import Primus.Core.Functor

@[ext]
structure NaturalTransformation{CC DD: Cat}(F G: Fun CC DD): Sort _ where
  η: (A: CC.Ob) -> DD.Hom (F A) (G A)
  naturality{A B: CC.Ob}(f: CC.Hom A B): η B ≪ F.onHom f = G.onHom f ≪ η A

instance {CC DD: Cat} {F G: Fun CC DD} :
    CoeFun (NaturalTransformation F G) (fun _ => ∀ A : CC.Ob, DD.Hom (F A) (G A)) where
  coe α := α.η

def natTransId{CC DD: Cat}(F: Fun CC DD): NaturalTransformation F F := {
  η A := DD.id (F A),
  naturality{A B} f := by
    rw [DD.left_id, DD.right_id]
}

def natTransComp{CC DD: Cat}{F G H: Fun CC DD}
  (ntG: NaturalTransformation G H)
  (ntF: NaturalTransformation F G): NaturalTransformation F H := {
  η A := ntG A ≪ ntF A,
  naturality{A B} f := by
    rw [DD.assoc, ←ntG.naturality f, ←DD.assoc, ntF.naturality f, DD.assoc]
  }

/-! The component lemmas. With these the laws below are proved through the
    `η` interface rather than by `unfold`ing the definitions and `cases`ing the
    transformations open. -/

@[simp] theorem natTransId_η{CC DD: Cat}(F: Fun CC DD)(A: CC.Ob):
  (natTransId F).η A = DD.id (F A)
:= rfl

@[simp] theorem natTransComp_η{CC DD: Cat}{F G H: Fun CC DD}
  (ntG: NaturalTransformation G H)(ntF: NaturalTransformation F G)(A: CC.Ob):
  (natTransComp ntG ntF).η A = ntG.η A ≪ ntF.η A
:= rfl

def functorCat(CC DD: Cat): Cat := {
  Ob := Fun CC DD,
  Hom := NaturalTransformation,
  id := natTransId,
  compose := natTransComp,
  left_id f := by ext A; simp
  right_id f := by ext A; simp
  assoc h g f := by ext A; apply DD.assoc
}
