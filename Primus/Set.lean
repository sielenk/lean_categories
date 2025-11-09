import Primus.Category
import Primus.Functor
import Primus.Discrete
import Primus.Two

import Mathlib.Data.Set.Image


def SetCat.{m}: category.{m+1, m} := {
  Ob := Sort m,
  Hom A B :=  A -> B,
  id _ := fun x => x,
  compose g f := g ∘ f
  left_id _ := rfl
  right_id _ := rfl
  assoc _ _ _ := rfl
}

def setTerminal: terminalObject SetCat := {
  T := PUnit
  hom X := fun _ => PUnit.unit
  unique g := by
    funext x
    cases g x
    rfl
}

def setInitial: initialObject SetCat := {
  I := PEmpty
  hom X := fun e => PEmpty.elim e
  unique g := by
    funext x
    cases x
}

def obToHom{A: SetCat.Ob}(x: A): SetCat.Hom (setTerminal.T) A :=
  fun _ => x

theorem obToHom_injective(A: SetCat.Ob): Function.Injective (@obToHom A) := by
  intro x1 x2 H1
  exact congrFun H1 PUnit.unit

theorem obToHom_surjective(A: SetCat.Ob): Function.Surjective (@obToHom A) := by
  intro f
  exists (f PUnit.unit)

theorem mono_injective{A B: SetCat.Ob}(f: SetCat.Hom A B):
  mono f ↔ Function.Injective f :=
by
  constructor
  · intro H1 x1 x2 H2
    rw [←@obToHom_injective A x1 x2]
    apply H1
    funext t
    assumption
  · intro H1 X g1 g2 H2
    funext x
    apply H1
    have H3: f (g1 x) = (SetCat.compose f g1) x := by rfl
    rw [H3, H2]
    rfl

theorem set_epi_surjective.{m}{A B: SetCat.{m+1}.Ob}(f: SetCat.Hom A B):
  epi f ↔ Function.Surjective f :=
by
  constructor
  · intro H1
    false_or_by_contra
    rename_i H2
    unfold Function.Surjective at H2
    rw [Classical.not_forall] at H2
    replace ⟨b, H2⟩ := H2
    replace H2: ∀ a, ¬f a = b := by
      intro a H3
      apply H2
      exists a
    let g1: SetCat.Hom B twoOb := fun b' => twoOb.ob1
    let g2: SetCat.Hom B twoOb := fun b' =>
      match Classical.propDecidable (b' = b) with
      | isTrue _  => twoOb.ob2
      | isFalse _ => twoOb.ob1
    have H3: g1 b = g2 b := by
      rw  [H1 g1 g2]
      funext a
      unfold SetCat g1 g2; simp
      cases Classical.propDecidable (f a = b)
      . rfl
      . exfalso
        apply H2 a
        assumption
    unfold g1 g2 at H3
    revert H3
    cases Classical.propDecidable (b = b)
    . contradiction
    . simp
  . intro H1 C g1 g2 H2
    funext b
    have ⟨a, H3⟩ := H1 b
    rw [←H3]
    have H4: (SetCat.compose g1 f) a = (SetCat.compose g2 f) a := by
      rw [H2]
    unfold SetCat at H4; simp at H4
    assumption

theorem set_splitEpi_surjective{A B: SetCat.Ob}(f: SetCat.Hom A B):
  splitEpi f ↔ Function.Surjective f :=
by
  constructor
  · intro ⟨g, H1⟩ b
    exists (g b)
    have H2: f (g b) = (SetCat.compose f g) b := by rfl
    rw [H2, H1]
    rfl
  . intro H1
    exists (fun b => Classical.choose (H1 b))
    funext b
    unfold SetCat
    simp
    exact Classical.choose_spec (H1 b)

theorem set_splitEpi_epi.{m}{A B: SetCat.{m+1}.Ob}(f: SetCat.Hom A B):
  epi f → splitEpi f :=
by
  rw [set_splitEpi_surjective, ←set_epi_surjective]
  tauto
