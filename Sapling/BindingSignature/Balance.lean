import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Sapling.Common.DiscreteLogRelation

/-!
# Binding-signature balance: the algebraic core

The algebraic core of the Sapling balance argument (Zcash protocol specification §4.13 "Balance
and Binding Signature (Sapling)"). A bundle whose net value is nonzero, and whose binding key `bvk`
has a known discrete log `bsk'`, yields an explicit nontrivial linear relation between the value
base `Vbase` and the randomness base `Rbase`.

This is proved in two stages: for a net value nonzero in the scalar field
(`NontrivialRelation.ofBundleModImbalance`), and for a nonzero integer net value of magnitude below
the field order (`NontrivialRelation.ofBundleIntImbalance`). The field stage is generic over a field
`F` acting on a group `M`; the integer stage fixes `F = ZMod r` for a prime `r`. Sapling takes
`r = ℓ`, the order of Jubjub's prime-order subgroup (the spec's `r_𝕁`; `jubjubScalarOrder` in
`Sapling.BindingSignature.Sapling`), and `M` that subgroup.

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
  verification is cofactored, so extraction gives only `[8] • bvk = [8] • (bsk' • Rbase)`;
  `§ Cofactored extraction` below derives the exact form from it. Obtaining the cofactored form by
  straight-line extraction in the algebraic group model needs two things this model does not
  provide: the fact that `[8]` maps the whole curve into the prime-order subgroup, and an adversary
  whose point representations may use the small-order points.
* **Value-commitment openings**: each spend and output comes with its opening `(v, rcv)`, which the
  spec obtains from Groth16 knowledge soundness and commitment binding.
* **Model of the curve**: Jubjub's prime-order subgroup is an abstract `F`-module `M` containing
  `Vbase` and `Rbase`, and the trapdoors `rcv` are scalars in `F`. Jubjub as an explicit curve, and
  the encoding of its points, are not modelled. The full curve, where it appears
  (`§ Cofactored extraction`), is an abstract group `G` into which `M` embeds injectively.
* **No overflow**: the integer net value has magnitude below `r` (the `hbound` hypothesis), which
  the spec's stronger range (within `ValueCommitType`) implies. For Sapling it is reduced to value
  ranges, the transaction size limit and the `vBalance` encoding by `sapling_natAbs_lt_of_bytes`
  in `Sapling.BindingSignature.Sapling`, which states those as its own assumptions.
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

/-- A nontrivial linear relation between `Vbase` and `Rbase`, as data: the shared
`Sapling.NontrivialRelation` at the two-point basis `![Vbase, Rbase]` with no generator family. Its
coefficients are `α` (of `Vbase`) and `β` (of `Rbase`), not both zero, with
`α • Vbase + β • Rbase = 0` (`relation_two`, `nontrivial_two`). Turning it into a discrete-log
solution is not done here. -/
-- Reading the relation: if `α ≠ 0`, then `Vbase = (−β / α) • Rbase`, a discrete log. If `α = 0`,
-- then `β • Rbase = 0` with `β ≠ 0`, impossible unless `Rbase = 0`. The spec's group hash never
-- returns the identity, so Sapling's `Rbase` is nonzero, but that is not proved here.
abbrev NontrivialRelation (Vbase Rbase : M) : Type _ :=
  Sapling.NontrivialRelation (F := F) (Fin.elim0 : Fin 0 → M) ![Vbase, Rbase]

/-- The relation in its two-point form: `α • Vbase + β • Rbase = 0`. The discrete-log reading
of a relation starts from this. -/
theorem NontrivialRelation.relation_two {Vbase Rbase : M}
    (rel : NontrivialRelation (F := F) Vbase Rbase) :
    rel.α • Vbase + rel.β • Rbase = 0 := by
  simpa [representationEval, augmentedBasis, Fintype.sum_sum_type, Fin.sum_univ_two,
    BasisIndex.u, BasisIndex.w] using rel.relation

/-- The coefficients in their two-point form are not both zero. -/
theorem NontrivialRelation.nontrivial_two {Vbase Rbase : M}
    (rel : NontrivialRelation (F := F) Vbase Rbase) :
    rel.α ≠ 0 ∨ rel.β ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  apply rel.nontrivial
  funext i
  rcases i with i | j
  · exact i.elim0
  · fin_cases j
    · exact h.1
    · exact h.2

/-- From `bvk = bsk' • Rbase` (`hExtract`),
`bvk = A • Vbase + B • Rbase` (`hSum`), and `A ≠ 0`, compute the nontrivial relation with
coefficients `(A, B − bsk')`. -/
def NontrivialRelation.ofImbalance (Vbase Rbase bvk : M) (A B bsk' : F) (hA : A ≠ 0)
    (hExtract : bvk = bsk' • Rbase) (hSum : bvk = A • Vbase + B • Rbase) :
    NontrivialRelation (F := F) Vbase Rbase :=
  Sapling.NontrivialRelation.ofParts Fin.elim0 ![A, B - bsk']
    (Or.inr (Function.ne_iff.mpr ⟨0, by simpa using hA⟩))
    (by
      simp only [commitGen, Fin.sum_univ_zero, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, zero_add]
      rw [smul_value_eq_smul_rand Vbase Rbase bvk A B bsk' hExtract hSum, ← add_smul]
      simp)

/-- **Bundle balance reduction (field level).** A bundle whose binding key has a known discrete
log `bsk'` (`hExtract`, the extracted-key assumption) and whose net value is nonzero in `F` (`hne`)
yields a nontrivial relation between `Vbase` and `Rbase`. The decomposition of `bvk` is derived by
`bindingVK_decomp`, not assumed. -/
def NontrivialRelation.ofBundleModImbalance (Vbase Rbase : M) (spends outputs : List (F × F))
    (vBalance bsk' : F)
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hExtract : bindingVK Vbase Rbase spends outputs vBalance = bsk' • Rbase) :
    NontrivialRelation (F := F) Vbase Rbase :=
  NontrivialRelation.ofImbalance Vbase Rbase (bindingVK Vbase Rbase spends outputs vBalance) _ _
    bsk' hne hExtract (bindingVK_decomp Vbase Rbase spends outputs vBalance)

/-! ### Integer balance: the no-overflow lift

The field-level reduction concerns the net value as an element of `ZMod r`, but balance is an
integer equation: `∑ spend values − ∑ output values − vBalance = 0` over `ℤ`. The second half of
spec §4.13 bridges the two: if the integer net value has magnitude below `r`, it cannot be a
nonzero multiple of `r`, so being `0` in `ZMod r` means being `0`. (The spec proves the stronger
range `vSum ∈ ValueCommitType`, which implies magnitude below `r`.) -/

/-- An integer that is `0` in `ZMod r` and has magnitude `< r` is `0`. -/
theorem intBalance_eq_zero_of_lt {r : ℕ} (N : ℤ)
    (hmod : (N : ZMod r) = 0) (hlt : N.natAbs < r) : N = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ((ZMod.intCast_zmod_eq_zero_iff_dvd N r).mp hmod)
    (by simpa using hlt)

/-- Cast a bundle with integer values (and field randomness) into the field, sending each value
`v : ℤ` to `(v : ZMod r)`. -/
def castBundle {r : ℕ} (l : List (ℤ × ZMod r)) : List (ZMod r × ZMod r) :=
  l.map fun p => ((p.1 : ZMod r), p.2)

/-- The value-sum of a cast bundle is the cast of the integer value-sum. -/
theorem castBundle_fst_sum {r : ℕ} (l : List (ℤ × ZMod r)) :
    ((castBundle l).map Prod.fst).sum = (((l.map Prod.fst).sum : ℤ) : ZMod r) := by
  induction l with
  | nil => simp [castBundle]
  | cons a t ih =>
    simp only [castBundle, List.map_cons, List.sum_cons, Int.cast_add] at ih ⊢
    rw [ih]

/-- **Bundle balance reduction (integer level).** A bundle with integer values whose binding key
has a known discrete log `bsk'` (`hExtract`, the extracted-key assumption), whose integer net value
is nonzero (`hne`), and whose net value has magnitude `< r` (`hbound`) yields a nontrivial
relation between `Vbase` and `Rbase`. -/
def NontrivialRelation.ofBundleIntImbalance {r : ℕ} [Fact (Nat.Prime r)]
    {M : Type*} [AddCommGroup M] [Module (ZMod r) M]
    (Vbase Rbase : M) (spends outputs : List (ℤ × ZMod r)) (vBalance : ℤ) (bsk' : ZMod r)
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hbound : ((spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance).natAbs < r)
    (hExtract : bindingVK Vbase Rbase (castBundle spends) (castBundle outputs) (vBalance : ZMod r)
      = bsk' • Rbase) :
    NontrivialRelation (F := ZMod r) Vbase Rbase :=
  have hne' : ((castBundle spends).map Prod.fst).sum - ((castBundle outputs).map Prod.fst).sum
      - (vBalance : ZMod r) ≠ 0 := fun hmod => by
    refine hne (intBalance_eq_zero_of_lt _ ?_ hbound)
    rw [castBundle_fst_sum, castBundle_fst_sum] at hmod
    rw [Int.cast_sub, Int.cast_sub]
    exact hmod
  NontrivialRelation.ofBundleModImbalance Vbase Rbase (castBundle spends) (castBundle outputs)
    (vBalance : ZMod r) bsk' hne' hExtract

/-! ### The generic overflow bound

The generic step toward the `hbound` hypothesis of `NontrivialRelation.ofBundleIntImbalance`. For
Sapling the values are the spend values followed by the negated output values (each still of
magnitude `≤ 2^64 − 1`), with one count `N` bounding spends and outputs together; that bridge is
`sapling_natAbs_lt` in `Sapling.BindingSignature.Sapling`.

The input bounds are looser than necessary, which is sound: `|vBalance| ≤ 2^63` admits one value
more than the signed 64-bit range `[−2^63, 2^63 − 1]`, and with `n` spends, `m` outputs and
`n + m ≤ N`, `vSumBound N` is at least the magnitude of every value in the spec's range
`[−m · (2^64 − 1) − 2^63 + 1, n · (2^64 − 1) + 2^63]` (§4.13). -/

/-- If every element of a list has `|x| ≤ c`, the sum has `|∑| ≤ length · c`. -/
theorem abs_listSum_le {l : List ℤ} {c : ℤ} (h : ∀ x ∈ l, |x| ≤ c) :
    |l.sum| ≤ (l.length : ℤ) * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : |a| ≤ c := h a List.mem_cons_self
    have ht : |t.sum| ≤ (t.length : ℤ) * c := ih fun x hx => h x (List.mem_cons_of_mem a hx)
    calc |(a :: t).sum| = |a + t.sum| := by rw [List.sum_cons]
      _ ≤ |a| + |t.sum| := abs_add_le a t.sum
      _ ≤ c + (t.length : ℤ) * c := add_le_add ha ht
      _ = ((a :: t).length : ℤ) * c := by rw [List.length_cons]; push_cast; ring

/-- From `|x| ≤ B` and `B < r`, the magnitude `x.natAbs < r`. -/
theorem natAbs_lt_of_abs_le {r : ℕ} {x B : ℤ} (hx : |x| ≤ B) (hr : B < (r : ℤ)) :
    x.natAbs < r := by
  have h : (x.natAbs : ℤ) < (r : ℤ) := by rw [← Int.abs_eq_natAbs]; exact lt_of_le_of_lt hx hr
  exact_mod_cast h

/-- The net-value magnitude bound for at most `N` values each with `|v| ≤ 2^64 − 1` and a
balance with `|vBalance| ≤ 2^63`: `N · (2^64 − 1) + 2^63`. -/
def vSumBound (N : ℕ) : ℤ := (N : ℤ) * (2^64 - 1) + 2^63

/-- **Generic no-overflow bound.** A list `vs` of at most `N` values, each with
`|v| ≤ 2^64 − 1`, and a balance with `|vBalance| ≤ 2^63` give `(vs.sum − vBalance).natAbs < r`
once `vSumBound N < r`. -/
theorem natAbs_lt_of_vSumBound {r : ℕ} (vs : List ℤ) (vBalance : ℤ) (N : ℕ)
    (hv : ∀ v ∈ vs, |v| ≤ 2^64 - 1)
    (hn : vs.length ≤ N)
    (hvb : |vBalance| ≤ 2^63)
    (hr : vSumBound N < (r : ℤ)) :
    (vs.sum - vBalance).natAbs < r := by
  refine natAbs_lt_of_abs_le ?_ hr
  simp only [vSumBound]
  have hlen : (vs.length : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn
  have hs : |vs.sum| ≤ (N : ℤ) * (2^64 - 1) :=
    le_trans (abs_listSum_le hv) (mul_le_mul_of_nonneg_right hlen (by norm_num))
  calc |vs.sum - vBalance| ≤ |vs.sum| + |vBalance| := abs_sub _ _
    _ ≤ (N : ℤ) * (2^64 - 1) + 2^63 := add_le_add hs hvb

/-! ### Cofactored extraction

Deployed RedJubjub verification is cofactored: it accepts a signature `(R, S)` with challenge `c`
when `[8] • (−S • Rbase + R + c • bvk) = 0` on the full curve, `8` being Jubjub's cofactor (spec
§5.4.7 "RedDSA, RedJubjub, and RedPallas", §5.4.7.2 "Binding Signature (Sapling and Orchard)",
§5.4.9.3 "Jubjub"). Jubjub has order `8 · r_𝕁`, so the `8` maps the check into the prime-order
subgroup and extraction yields `bsk'` only with `[8] • bvk = [8] • (bsk' • Rbase)`; that order is a
fact about Jubjub, not part of the model here. The `8` cancels for `bvk` in the prime-order
subgroup. Value commitments are points of the full curve (§4.1.8 "Commitment"), and the consensus
checks on the point itself reject only invalid encodings and small order (§4.4 "Spend Descriptions",
§4.5 "Output Descriptions"), so that membership comes from the value-commitment openings, and so
rests on the Spend and Output circuits binding each `cv` to its opening. -/

/-- Cofactor cancellation: `h • ι x = h • ι y` gives `x = y` when `ι : M →+ G` is injective and `h`
is nonzero in `F`. For Sapling, `M` is Jubjub's prime-order subgroup, `G` the full curve and
`h = 8`; `h` is a natural number because `G` is not an `F`-module. -/
theorem eq_of_nsmul_map_eq {G : Type*} [AddCommGroup G] (ι : M →+ G)
    (hι : Function.Injective ι) {h : ℕ} (hh : (h : F) ≠ 0) {x y : M}
    (hxy : h • ι x = h • ι y) : x = y := by
  rw [← map_nsmul, ← map_nsmul] at hxy
  have hM : (h : F) • x = (h : F) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]; exact hι hxy
  have := congrArg ((h : F)⁻¹ • ·) hM
  simpa only [smul_smul, inv_mul_cancel₀ hh, one_smul] using this

/-- The cofactored extraction `hExtract8` yields the exact `hExtract` of
`NontrivialRelation.ofBundleIntImbalance` through `eq_of_nsmul_map_eq`. -/
example {r : ℕ} [Fact (Nat.Prime r)] {M G : Type*} [AddCommGroup M] [Module (ZMod r) M]
    [AddCommGroup G] (ι : M →+ G) (hι : Function.Injective ι) {h : ℕ} (hh : (h : ZMod r) ≠ 0)
    (Vbase Rbase : M) (spends outputs : List (ℤ × ZMod r)) (vBalance : ℤ) (bsk' : ZMod r)
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hbound : ((spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance).natAbs < r)
    (hExtract8 : h • ι (bindingVK Vbase Rbase (castBundle spends) (castBundle outputs)
      (vBalance : ZMod r)) = h • ι (bsk' • Rbase)) :
    NontrivialRelation (F := ZMod r) Vbase Rbase :=
  NontrivialRelation.ofBundleIntImbalance Vbase Rbase spends outputs vBalance bsk' hne hbound
    (eq_of_nsmul_map_eq ι hι hh hExtract8)

end Sapling.BindingSignature
