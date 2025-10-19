structure category.{m, n}: Type _ where
  Ob: Type m
  Hom: Ob -> Ob -> Type n
  id(A:Ob): Hom A A
  compose{A B C: Ob}: Hom B C -> Hom A B -> Hom A C
  left_id {A B: Ob}(f: Hom A B): compose (id B) f = f
  right_id{A B: Ob}(f: Hom A B): compose f (id A) = f
  assoc{A B C D: Ob}(h: Hom C D)(g: Hom B C)(f: Hom A B):
         compose h (compose g f) = compose (compose h g) f

structure initialObject(CC: category): Type _ where
  I: CC.Ob
  hom(X: CC.Ob): CC.Hom I X
  unique{X: CC.Ob}(g: CC.Hom I X): hom X = g

structure terminalObject(CC: category): Type _ where
  T: CC.Ob
  hom(X: CC.Ob): CC.Hom X T
  unique{X: CC.Ob}(g: CC.Hom X T): hom X = g
