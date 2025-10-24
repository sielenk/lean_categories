import Primus.Category


def SetCat.{m}: category.{m+1, m} := {
  Ob := Sort m,
  Hom A B :=  A -> B,
  id _ := fun x => x,
  compose g f := g ∘ f
  left_id _ := rfl
  right_id _ := rfl
  assoc _ _ _ := rfl
}

def unitTerminal: terminalObject SetCat := {
  T := PUnit
  hom X := fun _ => PUnit.unit
  unique g := by
    funext x
    cases g x
    rfl
}

def emptyInitial: initialObject SetCat := {
  I := PEmpty
  hom X := fun e => PEmpty.elim e
  unique g := by
    funext x
    cases x
}

theorem mono_injective{A B: SetCat.Ob}(f: SetCat.Hom A B):
  mono f ↔ Function.Injective f := by
  constructor
  · intro H1 x1 x2 H2
    have H3: ∀(X: SetCat.Ob)(x: A), SetCat.compose f (fun _: X => x) = fun _ => f x := by
      intro X x
      rfl
    exact Hf
  · intro H1 X g1 g2 H2
    funext x
    apply H1
    have H3: (SetCat.compose f g1) x = f (g1 x) := by rfl
    rw [←H3, H2]
    rfl
