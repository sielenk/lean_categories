import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice

noncomputable section

open Classical
open Function
open Set

variable {α β : Type}
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0     => univ \ (g '' univ)
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

def sbFun[Nonempty β](x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sbRightInv[Nonempty β]{x : α}(hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have h1 : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    split_ands
    · simp
    · assumption
  have h2 : ∃ y, g y = x := by
    let ⟨y, ⟨_, hy⟩⟩ := h1
    use y
  apply invFun_eq h2

theorem sbInjective[Nonempty β](hf : Injective f) : Injective (sbFun f g) := by
  let A := sbSet f g
  let h := sbFun f g

  have h1: {x₁ x₂: α} → h x₁ = h x₂ → x₁ ∈ A → x₂ ∈ A := by
    intros x₁ x₂ hxeq h1
    have h2: h x₁ = f x₁ := by
      simp [h]
      simp [A] at h1
      rw [sbFun, if_pos h1]
    contrapose! h1
    have h3: h x₂ = invFun g x₂ := by
      simp [h]
      rw [sbFun, if_neg h1]
    rw [←hxeq, h2] at h3
    have h4: g (f x₁) = x₂ := by
      trans g (invFun g x₂)
      rw [h3]
      apply sbRightInv _ _ h1
    contrapose! h1
    simp [A, sbSet] at h1
    let ⟨n, hn⟩ := h1
    simp [A, sbSet]
    use n+1
    simp [sbAux]
    use x₁

  intro x₁ x₂ (hxeq : h x₁ = h x₂)

  by_cases h2 : x₁ ∈ A
  · apply hf
    have h3: x₂ ∈ A := h1 hxeq h2
    simp [h, sbFun] at hxeq
    rw [if_pos h2, if_pos h3] at hxeq
    assumption
  · have h3: x₂ ∉ A := by
      contrapose! h2
      apply h1 _ h2
      symm
      assumption
    simp [h, sbFun] at hxeq
    rw [if_neg h2, if_neg h3] at hxeq
    rw [← sbRightInv f g h2, ← sbRightInv f g h3, hxeq]


theorem sbSurjective[Nonempty β](hg : Injective g) : Surjective (sbFun f g) := by
  let A := sbSet f g
  let h := sbFun f g

  intro b
  by_cases h1 : g b ∈ A
  · simp [A, sbSet] at h1
    let ⟨n, h2⟩ := h1
    rcases n with _ | n
    · simp [sbAux] at h2
    · simp [sbAux] at h2
      let ⟨x, ⟨h2, h3⟩⟩ := h2
      use x
      have h4: x ∈ A := by
        simp [A, sbSet]
        use n
      simp [sbFun]
      rw [if_pos h4]
      apply hg h3
  · use g b
    simp [sbFun]
    rw [if_neg h1]
    apply hg
    apply sbRightInv f g h1


theorem schroederBernstein{f : α → β}{g : β → α}(hf : Injective f)(hg : Injective g) :
    ∃ h : α → β, Bijective h := by
  by_cases h1 : Nonempty β
  · exact ⟨sbFun f g, sbInjective f g hf, sbSurjective f g hg⟩
  · let h(a : α): β := False.elim (h1 ⟨f a⟩)
    exact ⟨h, ⟨λ a₁ _ => False.elim (h1 ⟨f a₁⟩), λ b => False.elim (h1 ⟨b⟩)⟩⟩

end
