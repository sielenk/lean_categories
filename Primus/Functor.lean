import Primus.Category
import Primus.Zero
import Primus.One


structure functor(CC DD: category) : Sort _ where
  onOb: CC.Ob -> DD.Ob
  onHom{A B: CC.Ob}: CC.Hom A B -> DD.Hom (onOb A) (onOb B)
  id{A: CC.Ob}: onHom (CC.id A) = DD.id (onOb A)
  compose{A B C: CC.Ob}{g: CC.Hom B C}{f: CC.Hom A B}:
         onHom (CC.compose g f) = DD.compose (onHom g) (onHom f)


section FunctorProperties
  variable {CC DD: category}
  variable (F: functor CC DD)

  def faithful: Prop :=
    ∀{A B: CC.Ob}, Function.Injective (@F.onHom A B)

  def full: Prop :=
    ∀{A B: CC.Ob}, Function.Surjective (@F.onHom A B)

  def fullyFaithful: Prop :=
    full F ∧ faithful F

  def essentiallySurjective: Prop :=
    ∀(D: DD.Ob), ∃(C: CC.Ob), isomorphic (F.onOb C) D

  def equivalence: Prop :=
    fullyFaithful F ∧ essentiallySurjective F

end FunctorProperties


def functorId(CC: category): functor CC CC := {
  onOb A := A,
  onHom{_ _} f:= f,
  id{A} := Eq.refl (CC.id A),
  compose{_ _ _ g f} := Eq.refl (CC.compose g f)
}

def functorComp{AA BB CC}(G: functor BB CC)(F: functor AA BB): functor AA CC := {
  onOb A := G.onOb (F.onOb A),
  onHom f := G.onHom (F.onHom f),
  id{A} := by
    rw [F.id, G.id],
  compose{A B C g f} := by
    rw [F.compose, G.compose]
}

def CategoryCat : category := {
  Ob := category,
  Hom := functor,
  id := functorId,
  compose := functorComp,
  left_id _ := by funext; rfl,
  right_id _ := by funext; rfl,
  assoc _ _ _ := by funext; rfl
}

def oneTerminal: terminalObject CategoryCat := {
  T := one,
  hom X := {
    onOb A := PUnit.unit,
    onHom f := PUnit.unit,
    id := rfl,
    compose := rfl
  },
  unique {CC} F := by
    congr
}

theorem faithful_comp{AA BB CC}(G: functor BB CC)(F: functor AA BB):
  faithful F ∧ faithful G → faithful (functorComp G F) := by
  intro ⟨H1, H2⟩ A B f1 f2 H3
  apply H1
  apply H2
  assumption

theorem full_comp{AA BB CC}(G: functor BB CC)(F: functor AA BB):
  full F ∧ full G → full (functorComp G F) := by
  intro ⟨H1, H2⟩ A B g
  let ⟨a, H3⟩ := (H2 g)
  let ⟨b, H4⟩ := (H1 a)
  exists b
  rw [←H3]
  unfold functorComp
  simp
  congr


def equivalent(CC DD: category): Prop :=
  ∃(F: functor CC DD), equivalence F
