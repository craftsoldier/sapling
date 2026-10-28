import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Binding-signature balance: the algebraic core

The algebraic heart of the Sapling balance argument (Zcash protocol specification §4.13 "Balance
and Binding Signature (Sapling)"): a bundle whose binding signature verifies and whose net value
is nonzero in the scalar field yields an explicit nontrivial linear relation between the value
base `Vbase` and the randomness base `Rbase`. This is balance modulo the field order only; the
integer statement also needs the no-overflow bound.

Generic over a field `F` acting on a group `M`; Sapling takes `F = ZMod ℓ` (the spec's `r_𝕁`) and
`M` the Jubjub prime-order subgroup.

The argument is the last step of the balance proof in Gabizon–Hopwood, *Sapling Security
Analysis* (2019).

Section numbers refer to the NU6.3 edition of the Zcash protocol specification.

## Assumptions

Taken as inputs, not proved:

* **Extracted key**: the reductions assume a `bsk'` with `bvk = bsk' • Rbase` (`hExtract`). A
  binding signature proves knowledge of such a key (spec §4.13), but computing `bsk'` from a signer
  needs a random oracle and an extraction argument, such as straight-line extraction in the
  algebraic group model (RedJubjub extractability), which is not formalized here. When
  `Rbase` generates a prime-order `M`, as in Sapling, such a `bsk'` always exists; what the
  assumption supplies is the key itself, so that the relation built from it is computed. Deployed
  verification is cofactored, so extraction gives only `[8] • bvk = [8] • (bsk' • Rbase)`; the
  exact form is not yet derived from it.
* **Value-commitment openings**: each spend and output comes with its opening `(v, rcv)`, which the
  spec obtains from Groth16 knowledge soundness and commitment binding.
* **Model of the curve**: Jubjub's prime-order subgroup is an abstract `F`-module `M` containing
  `Vbase` and `Rbase`, and the trapdoors `rcv` are scalars in `F`. Jubjub as an explicit curve, and
  the encoding of its points, are not modelled.
-/

namespace Sapling.BindingSignature

variable {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module F M]

/-! ### Value commitments and the binding verification key -/

/-- The value commitment `cv = v • Vbase + rcv • Rbase`. -/
def valueCommit (Vbase Rbase : M) (v rcv : F) : M := v • Vbase + rcv • Rbase

/-- A sum of value commitments is the value-sum times `Vbase` plus the randomness-sum times
`Rbase`. -/
theorem sum_valueCommit (Vbase Rbase : M) (l : List (F × F)) :
    (l.map fun p => valueCommit Vbase Rbase p.1 p.2).sum
      = (l.map Prod.fst).sum • Vbase + (l.map Prod.snd).sum • Rbase := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp only [valueCommit, add_smul]
    abel

/-- The binding verification key of a bundle:
`bvk = (∑ spend cv) − (∑ output cv) − vBalance • Vbase`. -/
def bindingVK (Vbase Rbase : M) (spends outputs : List (F × F)) (vBalance : F) : M :=
  (spends.map fun p => valueCommit Vbase Rbase p.1 p.2).sum
    - (outputs.map fun p => valueCommit Vbase Rbase p.1 p.2).sum - vBalance • Vbase

/-- **Binding-key decomposition.** `bvk = A • Vbase + B • Rbase`, with `A` the net value
(`∑ spend values − ∑ output values − vBalance`) and `B` the net randomness
(`∑ spend randomness − ∑ output randomness`). -/
theorem bindingVK_decomp (Vbase Rbase : M) (spends outputs : List (F × F)) (vBalance : F) :
    bindingVK Vbase Rbase spends outputs vBalance
      = ((spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance) • Vbase
        + ((spends.map Prod.snd).sum - (outputs.map Prod.snd).sum) • Rbase := by
  rw [bindingVK, sum_valueCommit, sum_valueCommit]
  simp only [sub_smul]
  abel

/-! ### Binding reduction -/

/-- From `bvk = bsk' • Rbase` and `bvk = A • Vbase + B • Rbase`, the value coefficient satisfies
`A • Vbase = (bsk' − B) • Rbase`. -/
theorem smul_value_eq_smul_rand (Vbase Rbase bvk : M) (A B bsk' : F)
    (hExtract : bvk = bsk' • Rbase) (hSum : bvk = A • Vbase + B • Rbase) :
    A • Vbase = (bsk' - B) • Rbase := by
  have h : A • Vbase + B • Rbase = bsk' • Rbase := by rw [← hSum, hExtract]
  rw [sub_smul, ← h, add_sub_cancel_right]

/-- A nontrivial linear relation between `Vbase` and `Rbase`, as data: coefficients `a`, `b`, not
both zero, with `a • Vbase + b • Rbase = 0`.

It is data rather than an `∃`: in a prime-order group such a relation always exists, so the content
of the reduction is that an unbalanced bundle lets us *compute* one.

When `a ≠ 0` it gives the discrete log `Vbase = (−b / a) • Rbase`. When `a = 0` it gives
`b • Rbase = 0` with `b ≠ 0`, which is impossible once `Rbase ≠ 0`, as it is for Sapling's
generators. The reduction from a relation to a discrete-log solution is not made here. -/
structure NontrivialRelation (F : Type*) [Field F] {M : Type*} [AddCommGroup M] [Module F M]
    (Vbase Rbase : M) where
  /-- The coefficient of `Vbase`. -/
  a : F
  /-- The coefficient of `Rbase`. -/
  b : F
  /-- The coefficients are not both zero. -/
  nontrivial : a ≠ 0 ∨ b ≠ 0
  /-- The relation itself. -/
  relation : a • Vbase + b • Rbase = 0

/-- **Balance reduction (field level).** From `bvk = bsk' • Rbase` (`hExtract`),
`bvk = A • Vbase + B • Rbase` (`hSum`), and `A ≠ 0`, compute the nontrivial relation with
coefficients `(A, B − bsk')`. -/
def NontrivialRelation.ofImbalance (Vbase Rbase bvk : M) (A B bsk' : F) (hA : A ≠ 0)
    (hExtract : bvk = bsk' • Rbase) (hSum : bvk = A • Vbase + B • Rbase) :
    NontrivialRelation F Vbase Rbase where
  a := A
  b := B - bsk'
  nontrivial := Or.inl hA
  relation := by
    rw [smul_value_eq_smul_rand Vbase Rbase bvk A B bsk' hExtract hSum, ← add_smul]
    simp

/-- **Bundle balance reduction (field level).** A bundle whose binding signature verifies
(`hExtract`) and whose net value is nonzero in `F` (`hne`) yields a nontrivial relation between
`Vbase` and `Rbase`. The decomposition of `bvk` is derived by `bindingVK_decomp`, not assumed. -/
def NontrivialRelation.ofBundleModImbalance (Vbase Rbase : M) (spends outputs : List (F × F))
    (vBalance bsk' : F)
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hExtract : bindingVK Vbase Rbase spends outputs vBalance = bsk' • Rbase) :
    NontrivialRelation F Vbase Rbase :=
  NontrivialRelation.ofImbalance Vbase Rbase (bindingVK Vbase Rbase spends outputs vBalance) _ _
    bsk' hne hExtract (bindingVK_decomp Vbase Rbase spends outputs vBalance)

end Sapling.BindingSignature
