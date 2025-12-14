import Primus.Category
import Primus.Functor
import Primus.Discrete
import Primus.Two
import Primus.EqualizerDiagram
import Primus.PullbackDiagram

import Mathlib.Data.Set.Image


def SortCat.{m}: category.{m+1, m} := {
  Ob := Sort m,
  Hom A B :=  A -> B,
  id _ x := x,
  compose g f x := g (f x)
  left_id _ := rfl
  right_id _ := rfl
  assoc _ _ _ := rfl
}

def sortTerminal: terminalObject SortCat := {
  T := PUnit
  hom X := fun _ => PUnit.unit
  unique X g := by
    funext x
    cases g x
    rfl
}

def sortInitial: initialObject SortCat := {
  I := PEmpty
  hom X := fun e => PEmpty.elim e
  unique X g := by
    funext x
    cases x
}

def obToHom{A: SortCat.Ob}(x: A): SortCat.Hom (sortTerminal.T) A :=
  fun _ => x

theorem obToHomInjective(A: SortCat.Ob): Function.Injective (@obToHom A) := by
  intro x1 x2 H1
  exact congrFun H1 PUnit.unit

theorem obToHomSurjective(A: SortCat.Ob): Function.Surjective (@obToHom A) := by
  intro f
  exists (f PUnit.unit)

theorem sortMonoInjective{A B: SortCat.Ob}(f: SortCat.Hom A B):
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
    have H3: f (g1 x) = (SortCat.compose f g1) x := by rfl
    rw [H3, H2]
    rfl

theorem sortEpiSurjective{A B: SortCat.{m+1}.Ob}(f: SortCat.Hom A B):
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
    let g1: SortCat.Hom B twoOb := fun b' => twoOb.ob1
    let g2: SortCat.Hom B twoOb := fun b' =>
      match Classical.propDecidable (b' = b) with
      | isTrue _  => twoOb.ob2
      | isFalse _ => twoOb.ob1
    intro H2
    have H3: g1 b = g2 b := by
      rw  [H2 g1 g2]
      funext a
      simp [SortCat]
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
    have H4: (SortCat.compose g1 f) a = (SortCat.compose g2 f) a := by
      rw [H2]
    simp [SortCat] at H4
    assumption

theorem sortSplitEpiSurjective{A B: SortCat.Ob}(f: SortCat.Hom A B):
  splitEpi f ↔ Function.Surjective f :=
by
  constructor
  · intro ⟨g, H1⟩ b
    use (g b)
    have H2: f (g b) = (SortCat.compose f g) b := by rfl
    rw [H2, H1]
    rfl
  · intro H1
    use (fun b => Classical.choose (H1 b))
    funext b
    unfold SortCat; simp
    exact Classical.choose_spec (H1 b)

theorem sortSplitEpiEpi.{m}{A B: SortCat.{m+1}.Ob}(f: SortCat.Hom A B):
  epi f → splitEpi f :=
by
  rw [sortSplitEpiSurjective, ←sortEpiSurjective]
  tauto


def sortCatEqualizer{X Y: SortCat.Ob}(f₁ f₂: SortCat.Hom X Y): equalizer f₁ f₂ := by
  let JJ := equalizerDiagram
  let CC := SortCat
  change CC.Ob at X Y
  change CC.Hom X Y at f₁ f₂
  let F: functor JJ CC := equalizerFunctor f₁ f₂
  let DD := coneCat F
  let E: CC.Ob := { x // f₁ x = f₂ x }
  let e: CC.Hom E X := Subtype.val
  let π i: CC.Hom E (F.onOb i) :=
    match i with
    | equalizerOb.A => e
    | equalizerOb.B => CC.compose f₁ e
  let H{J₁ J₂}(f : JJ.Hom J₁ J₂): CC.compose (F.onHom f) (π J₁) = π J₂ :=
    match f with
    | equalizerHom.idA => CC.left_id _
    | equalizerHom.idB => CC.left_id _
    | equalizerHom.f₁ => rfl
    | equalizerHom.f₂ => funext λ ⟨ee, H⟩ ↦ Eq.symm H
  let T: DD.Ob := coneOb.mk E π H
  let foo(T': DD.Ob): CC.Hom T'.N E := by
    let ⟨E', π', H'⟩ := T'
    let e':  CC.Hom E' X := π' equalizerOb.A
    let e'f: CC.Hom E' Y := π' equalizerOb.B
    change CC.Hom E' E
    intro ee'
    apply Subtype.mk (e' ee')
    let H₁: (λee ↦ f₁ (e' ee)) = e'f := @H' _ _ equalizerHom.f₁
    let H₂: (λee ↦ f₂ (e' ee)) = e'f := @H' _ _ equalizerHom.f₂
    trans e'f ee'
    · rw [←H₁]
    · rw [←H₂]

  let hom(T': DD.Ob): DD.Hom T' T := by
    apply coneHom.mk (foo T')
    let ⟨N', π', H'⟩ := T'
    intro jj
    simp [foo, CC, SortCat]
    ext x
    simp [T, π, e]
    cases jj
    · simp
    · simp [CC, SortCat]
      rw [←H' equalizerHom.f₁]
      simp [CC, SortCat, F]
      rfl

  let unique X: ∀g, g = hom X := by
    let ⟨Nx, πx, Hx⟩ := X
    simp [hom, foo]
    intro ⟨g, Hg⟩
    simp [CC, SortCat, T, E] at g Hg
    congr
    simp [CC, SortCat, T, E]
    ext x
    have H2 : πx equalizerOb.A x = π equalizerOb.A (g x) := by
      rw [←Hg equalizerOb.A]
    congr!
    rw [H2]

  exact {
    T := T
    hom := hom
    unique := unique
  }

def sortCatPullback{X₁ X₂ Y: SortCat.Ob}
  (f₁: SortCat.Hom X₁ Y)(f₂: SortCat.Hom X₂ Y): pullback f₁ f₂ :=
by
  refine {
    T := {
      N := { xx: X₁ × X₂ // f₁ xx.1 = f₂ xx.2 }
      π J X := match J with
        | pullbackOb.A₁ => X.val.1
        | pullbackOb.A₂ => X.val.2
        | pullbackOb.B => f₁ X.val.1
      comm f := match f with
        | pullbackHom.idA₁ => SortCat.left_id _
        | pullbackHom.idA₂ => SortCat.left_id _
        | pullbackHom.idB => SortCat.left_id _
        | pullbackHom.f₁ => rfl
        | pullbackHom.f₂ => funext (λ N => Eq.symm N.property)
    }
    hom X := {
      h x := ⟨
        ⟨X.π pullbackOb.A₁ x, X.π pullbackOb.A₂ x⟩,
        Eq.trans
          (congrArg (λ h => h x) (X.comm pullbackHom.f₁))
          (Eq.symm
            (congrArg (λ h => h x) (X.comm pullbackHom.f₂))
          )
      ⟩
      fac J := match J with
        | pullbackOb.A₁ => rfl
        | pullbackOb.A₂ => rfl
        | pullbackOb.B =>
          funext (λ x => congrArg (λ h => h x) (X.comm pullbackHom.f₁))
    }
    unique X g := ?unique
  }
  · case unique =>
    trans ⟨g.h, g.fac⟩
    · rfl
    · congr
      funext x
      apply Subtype.ext
      apply Prod.ext
      · apply congrArg (λ h => h x) (g.fac pullbackOb.A₁)
      · apply congrArg (λ h => h x) (g.fac pullbackOb.A₂)
