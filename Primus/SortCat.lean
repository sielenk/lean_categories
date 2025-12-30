import Primus.Category
import Primus.Functor
import Primus.Discrete
import Primus.Two
import Primus.EqualizerDiagram
import Primus.PullbackDiagram

import Mathlib.Data.Set.Image


def sortCat.{m}: Cat.{m+1, m} := {
  Ob := Sort m,
  Hom A B :=  A -> B,
  id _ x := x,
  compose g f x := g (f x)
  left_id _ := rfl
  right_id _ := rfl
  assoc _ _ _ := rfl
}

def sortCat.initial: InitialObject sortCat := {
  I := PEmpty
  hom X := fun e => PEmpty.elim e
  unique X g := by
    funext x
    cases x
}

def sortCat.terminal: TerminalObject sortCat := {
  T := PUnit
  hom X := fun _ => PUnit.unit
  unique X g := by
    funext x
    cases g x
    rfl
}

def obToHom{A: sortCat.Ob}(x: A): sortCat.Hom sortCat.terminal A :=
  fun _ => x

theorem obToHomInjective(A: sortCat.Ob): Function.Injective (@obToHom A) := by
  intro x1 x2 H1
  exact congrFun H1 PUnit.unit

theorem obToHomSurjective(A: sortCat.Ob): Function.Surjective (@obToHom A) := by
  intro f
  exists (f PUnit.unit)

theorem sortMonoInjective{A B: sortCat.Ob}(f: sortCat.Hom A B):
  mono f ↔ Function.Injective f :=
by
  constructor
  · intro H1 x1 x2 H2
    rw [←@obToHomInjective A x1 x2]
    apply H1
    funext t
    assumption
  · intro H1 X g1 g2 H2
    funext x
    apply H1
    have H3: f (g1 x) = (sortCat.compose f g1) x := by rfl
    rw [H3, H2]
    rfl

theorem sortEpiSurjective{A B: sortCat.{m+1}.Ob}(f: sortCat.Hom A B):
  epi f ↔ Function.Surjective f :=
by
  constructor
  · contrapose
    intro H1
    unfold Function.Surjective at H1
    rw [Classical.not_forall] at H1
    replace ⟨b, H1⟩ := H1
    replace H1: ∀ a, ¬f a = b := by
      intro a H2
      apply H1
      use a
    let g1: sortCat.Hom B TwoOb := fun b' => TwoOb.ob1
    let g2: sortCat.Hom B TwoOb := fun b' =>
      match Classical.propDecidable (b' = b) with
      | isTrue _  => TwoOb.ob2
      | isFalse _ => TwoOb.ob1
    intro H2
    have H3: g1 b = g2 b := by
      rw  [H2 g1 g2]
      funext a
      simp [sortCat]
      unfold g1 g2
      cases Classical.propDecidable (f a = b) with
      | isFalse H =>
        rfl
      | isTrue H =>
        exfalso
        exact H1 a H
    unfold g1 g2 at H3
    revert H3
    cases Classical.propDecidable (b = b) with
    | isFalse H =>
      contradiction
    | isTrue H =>
      simp
  · intro H1 C g1 g2 H2
    funext b
    have ⟨a, H3⟩ := H1 b
    rw [←H3]
    have H4: (sortCat.compose g1 f) a = (sortCat.compose g2 f) a := by
      rw [H2]
    simp [sortCat] at H4
    assumption

theorem sortSplitEpiSurjective{A B: sortCat.Ob}(f: sortCat.Hom A B):
  splitEpi f ↔ Function.Surjective f :=
by
  constructor
  · intro ⟨g, H1⟩ b
    use (g b)
    have H2: f (g b) = (sortCat.compose f g) b := by rfl
    rw [H2, H1]
    rfl
  · intro H1
    use (fun b => Classical.choose (H1 b))
    funext b
    unfold sortCat; simp
    exact Classical.choose_spec (H1 b)

theorem sortSplitEpiEpi.{m}{A B: sortCat.{m+1}.Ob}(f: sortCat.Hom A B):
  epi f → splitEpi f :=
by
  rw [sortSplitEpiSurjective, ←sortEpiSurjective]
  tauto


def sortCat.Equalizer{X Y: sortCat.Ob}(f₁ f₂: sortCat.Hom X Y): Equalizer f₁ f₂ :=
  {
    T := {
      N := { x // f₁ x = f₂ x }
      π J X := match J with
        | EqualizerOb.A => X.val
        | EqualizerOb.B => f₁ X.val
      comm f := match f with
        | EqualizerHom.idA => sortCat.left_id _
        | EqualizerHom.idB => sortCat.left_id _
        | EqualizerHom.f₁ => rfl
        | EqualizerHom.f₂ => funext (λ N => Eq.symm N.property)
    }
    hom X := {
      h x := ⟨
        X.π EqualizerOb.A x,
         Eq.trans
          (congrArg (λ h => h x) (X.comm EqualizerHom.f₁))
          (Eq.symm
            (congrArg (λ h => h x) (X.comm EqualizerHom.f₂))
          )
      ⟩
      fac J := match J with
        | EqualizerOb.A => rfl
        | EqualizerOb.B => X.comm EqualizerHom.f₁
    }
    unique _ g :=
      ConeHom.ext (funext (λ_ => Subtype.ext (congr_fun (g.fac EqualizerOb.A) _)))
  }

def sortCat.Pullback{X₁ X₂ Y: sortCat.Ob}
  (f₁: sortCat.Hom X₁ Y)(f₂: sortCat.Hom X₂ Y): Pullback f₁ f₂ :=
by
  refine {
    T := {
      N := { xx: X₁ × X₂ // f₁ xx.1 = f₂ xx.2 }
      π J X := match J with
        | PullbackOb.A₁ => X.val.1
        | PullbackOb.A₂ => X.val.2
        | PullbackOb.B => f₁ X.val.1
      comm f := match f with
        | PullbackHom.idA₁ => sortCat.left_id _
        | PullbackHom.idA₂ => sortCat.left_id _
        | PullbackHom.idB => sortCat.left_id _
        | PullbackHom.f₁ => rfl
        | PullbackHom.f₂ => funext (λ N => Eq.symm N.property)
    }
    hom X := {
      h x := ⟨
        ⟨X.π PullbackOb.A₁ x, X.π PullbackOb.A₂ x⟩,
        Eq.trans
          (congrArg (λ h => h x) (X.comm PullbackHom.f₁))
          (Eq.symm
            (congrArg (λ h => h x) (X.comm PullbackHom.f₂))
          )
      ⟩
      fac J := match J with
        | PullbackOb.A₁ => rfl
        | PullbackOb.A₂ => rfl
        | PullbackOb.B => X.comm PullbackHom.f₁
    }
    unique X g := ?unique
  }
  · case unique =>
    apply ConeHom.ext
    funext x
    apply Subtype.ext
    apply Prod.ext
    · apply congrArg (λ h => h x) (g.fac PullbackOb.A₁)
    · apply congrArg (λ h => h x) (g.fac PullbackOb.A₂)
