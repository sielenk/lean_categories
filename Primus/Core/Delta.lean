import Primus.Core.Category
import Primus.Core.Functor
import Primus.Core.NatTrans


def delta JJ {CC}(C: CC.Ob): Fun JJ CC := {
  onOb _ := C,
  onHom _ := CC.id C,
  id := Eq.refl (CC.id C),
  compose := Eq.symm (CC.left_id _)
}

def deltaFun JJ CC: Fun CC (functorCat JJ CC) := {
  onOb := delta JJ,
  onHom f := {
    η _ := f,
    naturality _ := Eq.trans (CC.right_id f) (Eq.symm (CC.left_id f))
  },
  id := Eq.refl _,
  compose := Eq.refl _
}
