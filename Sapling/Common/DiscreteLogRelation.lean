import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fintype.BigOperators

/-!
# Nontrivial linear (discrete-log) relations, as computed data

A nontrivial `F`-linear relation among a family of group elements, carried as *data* (the
coefficients) so that a reduction can compute it rather than merely assert that it exists. In a
prime-order group such a relation always exists, so an `∃`-closed `Prop` would be vacuous; the
content of a reduction is that it produces one.

`AlgebraicRelationWitness` is the underlying type: a nonzero coefficient vector over a finite index
whose combination of the basis is zero. A commitment scheme presents a generator family `g`
alongside distinguished points `V`; `BasisIndex n J` names the slots of such a basis, and
`NontrivialRelation g V` is `AlgebraicRelationWitness` at it.
-/

namespace Sapling

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- Evaluate a representation over a finite basis: `∑ i, coeffs i • basis i`. -/
def representationEval {ι : Type*} [Fintype ι] (basis : ι → G) (coeffs : ι → F) : G :=
  ∑ i, coeffs i • basis i

/-- Nonzero coefficients whose combination of `basis` is zero. -/
structure AlgebraicRelationWitness {ι : Type*} [Fintype ι] (basis : ι → G) where
  /-- The coefficient at each basis slot. -/
  coeffs : ι → F
  /-- The coefficients are not all zero. -/
  nontrivial : coeffs ≠ 0
  /-- The relation itself. -/
  relation : representationEval basis coeffs = 0

/-- The commitment over generators `g`: `∑ i, a i • g i`. -/
def commitGen {n : ℕ} (g : Fin n → G) (a : Fin n → F) : G := ∑ i, a i • g i

/-- The index of a presented basis: `n` generator slots, plus a distinguished slot for each
member of `J`. -/
abbrev BasisIndex (n : ℕ) (J : Type*) := Sum (Fin n) J

namespace BasisIndex

/-- The slot for a family generator. -/
def gen {n : ℕ} {J : Type*} (i : Fin n) : BasisIndex n J := Sum.inl i

/-- The slot for the first distinguished point (`U` in a `(g, U, W)` basis). -/
def u {n k : ℕ} : BasisIndex n (Fin (k + 1)) := Sum.inr 0

/-- The slot for the second distinguished point (`W` in a `(g, U, W)` basis). -/
def w {n k : ℕ} : BasisIndex n (Fin (k + 2)) := Sum.inr 1

end BasisIndex

/-- A generator family `g` augmented by the distinguished points `V`, as one indexed basis. -/
def augmentedBasis {n : ℕ} {J : Type*} (g : Fin n → G) (V : J → G) : BasisIndex n J → G :=
  Sum.elim g V

/-- One coefficient vector over the augmented basis, from its generator and distinguished
parts. -/
def augmentedCoeffs {n : ℕ} {J : Type*} (a : Fin n → F) (c : J → F) : BasisIndex n J → F :=
  Sum.elim a c

/-- Evaluating an augmented representation is the generator combination plus the distinguished
combination. -/
theorem representationEval_augmentedBasis {n : ℕ} {J : Type*} [Fintype J]
    (g : Fin n → G) (V : J → G) (a : Fin n → F) (c : J → F) :
    representationEval (augmentedBasis g V) (augmentedCoeffs a c) =
      commitGen g a + ∑ j, c j • V j := by
  simp [representationEval, augmentedBasis, augmentedCoeffs, commitGen, Fintype.sum_sum_type]

/-- A nontrivial `F`-linear (discrete-log) relation among the generators `g` and the distinguished
points `V`: `AlgebraicRelationWitness` at the augmented basis. Build one with
`NontrivialRelation.ofParts`; at a two-point basis `![U, W]`, read the distinguished coefficients
with `α` and `β`. -/
abbrev NontrivialRelation {n : ℕ} {J : Type*} [Fintype J] (g : Fin n → G) (V : J → G) :
    Type _ :=
  AlgebraicRelationWitness (F := F) (augmentedBasis g V)

/-- Assemble a relation from its parts: generator coefficients `a` and distinguished coefficients
`c`, not all zero, sending the basis to `0`. -/
def NontrivialRelation.ofParts {n : ℕ} {J : Type*} [Fintype J] {g : Fin n → G}
    {V : J → G} (a : Fin n → F) (c : J → F)
    (hnontrivial : a ≠ 0 ∨ c ≠ 0)
    (hrelation : commitGen g a + ∑ j, c j • V j = 0) :
    NontrivialRelation (F := F) g V where
  coeffs := augmentedCoeffs a c
  nontrivial := by
    rcases hnontrivial with ha | hc
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
      exact Function.ne_iff.mpr ⟨BasisIndex.gen i,
        by simpa [BasisIndex.gen, augmentedCoeffs] using hi⟩
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
      exact Function.ne_iff.mpr ⟨Sum.inr j, by simpa [augmentedCoeffs] using hj⟩
  relation := by rw [representationEval_augmentedBasis]; exact hrelation

/-- The coefficient at the first distinguished slot. -/
abbrev NontrivialRelation.α {n k : ℕ} {g : Fin n → G} {V : Fin (k + 1) → G}
    (r : NontrivialRelation (F := F) g V) : F :=
  r.coeffs BasisIndex.u

/-- The coefficient at the second distinguished slot. -/
abbrev NontrivialRelation.β {n k : ℕ} {g : Fin n → G} {V : Fin (k + 2) → G}
    (r : NontrivialRelation (F := F) g V) : F :=
  r.coeffs BasisIndex.w

end Sapling
