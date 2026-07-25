structure Cat.{m, n}: Sort _ where
  Ob: Sort m
  Hom: Ob -> Ob -> Sort n
  id(A:Ob): Hom A A
  compose{A B C: Ob}: Hom B C -> Hom A B -> Hom A C
  left_id {A B: Ob}(f: Hom A B): compose (id B) f = f
  right_id{A B: Ob}(f: Hom A B): compose f (id A) = f
  assoc{A B C D: Ob}(h: Hom C D)(g: Hom B C)(f: Hom A B):
         compose h (compose g f) = compose (compose h g) f

attribute [simp] Cat.left_id Cat.right_id


structure InitialObject(CC: Cat): Sort _ where
  I: CC.Ob
  hom(X: CC.Ob): CC.Hom I X
  unique(X: CC.Ob): ∀g: CC.Hom I X, g = hom X

attribute [coe] InitialObject.I
instance{CC}: Coe (InitialObject CC) CC.Ob where coe i := i.I

@[ext]
theorem InitialObject.ext{CC: Cat}{A B: InitialObject CC}: A.I = B.I -> A = B := by
  let ⟨I, ha, Ha⟩ := A
  let ⟨I', hb, Hb⟩ := B
  simp
  intro H
  subst H
  constructor
  . rfl
  . apply heq_of_eq
    funext X
    apply Hb


structure TerminalObject(CC: Cat): Sort _ where
  T: CC.Ob
  hom(X: CC.Ob): CC.Hom X T
  unique(X: CC.Ob): ∀g, g = hom X

attribute [coe] TerminalObject.T
instance{CC}: Coe (TerminalObject CC) CC.Ob where coe t := t.T

@[ext]
theorem TerminalObject.ext{CC: Cat}{A B: TerminalObject CC}: A.T = B.T -> A = B := by
  let ⟨T, ha, Ha⟩ := A
  let ⟨T', hb, Hb⟩ := B
  simp
  intro H
  subst H
  constructor
  · rfl
  · apply heq_of_eq
    funext X
    apply Hb


def isomorphic{CC: Cat}(A B: CC.Ob): Prop :=
  ∃(f: CC.Hom A B)(g: CC.Hom B A), CC.compose g f = CC.id A ∧ CC.compose f g = CC.id B

def skeletal(CC: Cat): Prop :=
  ∀(A B: CC.Ob), isomorphic A B -> A = B

def thin(CC: Cat): Prop :=
  ∀(A B: CC.Ob)(f₁ f₂: CC.Hom A B), f₁ = f₂


section MorphismProperties
  variable {CC: Cat}
  variable {A B: CC.Ob}
  variable (f: CC.Hom A B)

  def mono: Prop :=
    ∀{X: CC.Ob}(g1 g2: CC.Hom X A), CC.compose f g1 = CC.compose f g2 → g1 = g2

  def epi: Prop :=
    ∀{X: CC.Ob}(g1 g2: CC.Hom B X), CC.compose g1 f = CC.compose g2 f → g1 = g2

  def splitMono: Prop :=
    ∃(g: CC.Hom B A), CC.compose g f = CC.id A

  def splitEpi: Prop :=
    ∃(g: CC.Hom B A), CC.compose f g = CC.id B

  def inverse(g: CC.Hom B A): Prop :=
    CC.compose g f = CC.id A ∧ CC.compose f g = CC.id B

  def iso: Prop :=
    ∃(g: CC.Hom B A), inverse f g

end MorphismProperties


theorem splitMonoIsMono{CC: Cat}{A B: CC.Ob}(f: CC.Hom A B):
  splitMono f → mono f := by
  intro ⟨g, H1⟩ X g1 g2 H2
  rw [←CC.left_id g1, ←CC.left_id g2, ←H1, ←CC.assoc, ←CC.assoc, H2]

theorem splitEpiIsEpi{CC: Cat}{A B: CC.Ob}(f: CC.Hom A B):
  splitEpi f → epi f := by
  intro ⟨g, H1⟩ X g1 g2 H2
  rw [←CC.right_id g1, ←CC.right_id g2, ←H1, CC.assoc, CC.assoc, H2]

theorem splitMonoEpiIsIso{CC: Cat}{A B: CC.Ob}(f: CC.Hom A B):
  splitMono f ∧ epi f → iso f := by
  intro ⟨⟨g, H1⟩, H2⟩
  apply Exists.intro g
  and_intros
  · assumption
  · apply H2
    rw [←CC.assoc, H1]
    simp

theorem splitEpiMonoIsIso{CC: Cat}{A B: CC.Ob}(f: CC.Hom A B):
  splitEpi f ∧ mono f → iso f := by
  intro ⟨⟨g, H1⟩, H2⟩
  apply Exists.intro g
  and_intros
  · apply H2
    rw [CC.assoc, H1]
    simp
  · assumption
