import Mathlib.Data.Set

/--
The Schröder–Bernstein theorem: If there exist injective functions `f : X → Y` and `g : Y → X`,
then there exists a bijective function `h : X → Y`.
-/
theorem schroederBernstein {X Y : Set} (f : X → Y) (g : Y → X)
  (hf : Function.Injective f) (hg : Function.Injective g) :
  ∃ h : X → Y, Function.bijective h :=
by
  let A : Set := { x ∈ X | ∃ n : ℕ, (g ∘ f)^[n] x ∉ range g }
  let B : Set := { y ∈ Y | ∃ n : ℕ, (f ∘ g)^[n] y ∉ range f }
  have hAB : f '' A = B :=
    by
      ext y
      constructor
      · rintro ⟨x, ⟨hxX, hxA⟩, rfl⟩
        use (f x), ⟨f x, by simp [hxX]⟩
        use 0
        simp [hxA]
      · rintro ⟨y, ⟨hyY, hyB⟩, rfl⟩
        rcases hyB with ⟨n, hn⟩
        use (g y), ⟨g y, by simp [hyY]⟩
        use n + 1
        simp [hn]
  let h : X → Y := fun x => if x ∈ A then f x else (g⁻¹) x
  use h
  constructor
  · intro y
    by_cases hyB : y ∈ B
    · rcases hyB with ⟨y', ⟨hy'Y, hy'B⟩, rfl⟩
      use y'
      simp [hAB] at hyB
      simp [hAB] at hy'B
      simp [hAB] at hy'B
      have : y' ∈ A := by simpa using hy'B
      simp [h, this]
    · rcases hg (by simpa using hyB) with ⟨x', hx'X, rfl⟩
      use x'
      simp [h, hyB]
  · intro x₁ x₂ hx₁ hx₂ hxx
    by_cases hx₁A : x₁ ∈ A; by_cases hx₂A : x₂ ∈ A
    · have : f x₁ = f x₂ := by simp [h, hx₁A, hx₂A] at hxx; exact hxx
      exact hf this
    · have : (g
