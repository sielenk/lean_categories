universe m n

structure category: Type max (m+1) (n+1) where
  Ob: Type m
  Hom: Ob -> Ob -> Type n
  id(A:Ob): Hom A A
  compose{A B C: Ob}: Hom B C -> Hom A B -> Hom A C
  left_id {A B: Ob}(f: Hom A B): compose (id B) f = f
  right_id{A B: Ob}(f: Hom A B): compose f (id A) = f
  assoc{A B C D: Ob}(h: Hom C D)(g: Hom B C)(f: Hom A B):
         compose h (compose g f) = compose (compose h g) f

structure functor(CC DD: category.{m, n}) : Type max m n where
  onOb: CC.Ob -> DD.Ob
  onHom{A B: CC.Ob}: CC.Hom A B -> DD.Hom (onOb A) (onOb B)
  id{A: CC.Ob}: onHom (CC.id A) = DD.id (onOb A)
  compose{A B C: CC.Ob}{f: CC.Hom A B}{g: CC.Hom B C}:
         onHom (CC.compose g f) = DD.compose (onHom g) (onHom f)

structure naturalTransformation{CC DD: category.{m, n}}(FF GG: functor.{m, n} CC DD): Type max (m+1) (n+1) where
  eta: (A: CC.Ob) -> DD.Hom (FF.onOb A) (GG.onOb A)
  naturality{A B: CC.Ob}(f: CC.Hom A B): DD.compose (eta B) (FF.onHom f) = DD.compose (GG.onHom f) (eta A)


structure initialObject(CC: category.{m, n}): Type max (m+1) (n+1) where
  I: CC.Ob
  hom(X: CC.Ob): CC.Hom I X
  unique{X: CC.Ob}(g: CC.Hom I X): hom X = g

structure terminalObject(CC: category.{m, n}): Type max (m+1) (n+1) where
  T: CC.Ob
  hom(X: CC.Ob): CC.Hom X T
  unique{X: CC.Ob}(g: CC.Hom X T): hom X = g
