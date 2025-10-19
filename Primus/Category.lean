structure category.{m, n}: Sort _ where
  Ob: Sort m
  Hom: Ob -> Ob -> Sort n
  id(A:Ob): Hom A A
  compose{A B C: Ob}: Hom B C -> Hom A B -> Hom A C
  left_id {A B: Ob}(f: Hom A B): compose (id B) f = f
  right_id{A B: Ob}(f: Hom A B): compose f (id A) = f
  assoc{A B C D: Ob}(h: Hom C D)(g: Hom B C)(f: Hom A B):
         compose h (compose g f) = compose (compose h g) f

attribute [simp] category.left_id category.right_id

structure initialObject(CC: category): Sort _ where
  I: CC.Ob
  hom(X: CC.Ob): CC.Hom I X
  unique{X: CC.Ob}(g: CC.Hom I X): hom X = g

structure terminalObject(CC: category): Sort _ where
  T: CC.Ob
  hom(X: CC.Ob): CC.Hom X T
  unique{X: CC.Ob}(g: CC.Hom X T): hom X = g
