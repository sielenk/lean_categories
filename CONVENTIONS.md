# Conventions

## Naming

| Kind | Convention | Examples |
|------|-----------|---------|
| Inductive types, structures | `PascalCase` | `Cat`, `Fun`, `ConeOb`, `NaturalTransformation` |
| Category/functor/def values | `camelCase` | `sortCat`, `two`, `equalizerDiagram`, `functorId` |
| Namespace-qualified constructions | dot notation | `sortCat.Lim`, `sortCat.Equalizer`, `propCat.Limit` |
| Theorem names | `snake_case` | `split_mono_is_mono`, `yoneda_fully_faithful` |

**Migration goals:**
- Rename `PropLimit`, `PropCoLimit` to `propCat.Limit`, `propCat.CoLimit` to match the dot-notation style established in `SortCat`.
- Rename theorems from `camelCase` (e.g. `splitMonoIsMono`) to `snake_case` (e.g. `split_mono_is_mono`) to match Lean 4 / Mathlib conventions. The current style predates awareness of this convention.

## Module structure

```
Primus/
  Core/       Base structures: Cat, Fun, NatTrans, Opposite, Product, Comma, Delta
  Diagrams/   Diagram shapes: ordinals (Zero–Four), Discrete, Nat,
              EqualizerDiagram, PullbackDiagram
  Limits/     Cone, CoCone, Lim, CoLim
  Instances/  Concrete categories: SortCat, PropCat
  Yoneda/     Hom functor and Yoneda lemma
```

## Diagram shapes

The ordinal categories are the representable objects of the simplex category Δ:

| File | Category | Purpose |
|------|----------|---------|
| `Zero` | ∅ | empty category |
| `One` | [0] | single object; terminal in `Cat` |
| `Two` | [1] | walking morphism |
| `Three` | [2] | walking composable pair (composition) |
| `Four` | [3] | walking composable triple (associativity) |
