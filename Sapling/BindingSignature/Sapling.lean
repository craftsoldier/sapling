import CompElliptic.Fields.Jubjub
import Mathlib.Tactic.Linarith
import Sapling.BindingSignature.Balance

/-!
# Sapling's no-overflow bound and balance reduction

The Sapling instance of the no-overflow lift (spec §4.13 "Balance and Binding Signature
(Sapling)"). A bundle whose descriptions fit in one transaction has an integer net value of
magnitude far below the Jubjub scalar order `ℓ`: about `2^77` against `2^252`. Applied to a
bundle's spend and output values at `r = ℓ`, `sapling_natAbs_lt_of_bytes` gives exactly the
`hbound` hypothesis of `NontrivialRelation.ofBundleIntImbalance`, and
`NontrivialRelation.ofSaplingImbalance` composes the two, taking the key in its exact form.
`NontrivialRelation.ofSaplingBundle` takes instead the commitments the transaction carries and the
cofactored equation on the verifier's key, and derives the exact form through
`verifierBVK_of_openings` and `eq_of_nsmul_map_eq`, with `eight_ne_zero_jubjub` supplying that
Jubjub's cofactor `8` is nonzero mod `ℓ`. An `example` after each checks that its hypotheses can
hold together.

The spend and output counts come from the 2 MB transaction size limit and each description's
minimum encoded size, summed field by field from the spec's encoding tables, with each result tied
to the spec's stated value by an `example`. Version 6 transactions use the version 5 Sapling layout.

Section numbers refer to the NU6.3 edition of the Zcash protocol specification.

## Assumptions

Taken as inputs, not proved:

* **Extracted key, value-commitment openings, model of the curve**:
  `NontrivialRelation.ofSaplingBundle` takes a key `bsk'` satisfying the cofactored equation
  (`hExtract8`), the openings `spends` and `outputs` of the commitments `cvIn` and `cvOut` (`hcvIn`,
  `hcvOut`), an abstract module `M`, and an injective `ι : M →+ G` into an abstract group `G`, as
  described in the Assumptions of `Sapling.BindingSignature.Balance`.
  `NontrivialRelation.ofSaplingImbalance` takes the key in its exact form (`hExtract`).
* **Value ranges**: every spend and output value is in `[0, 2^64 − 1]` (`hOld`, `hNew`). The spend
  and output circuits enforce this for the values they commit to. Each note's value is also at
  most `MAX_MONEY`, a smaller bound, but the circuits check only 64 bits, the range §4.13 uses.
* **Encoding sizes**: the spends and outputs fit in one transaction of at most `maxTxBytes` bytes
  (`hSpend`, `hOutput`), a consensus limit together with the transaction encoding.
* **Balance range**: `|vBalance| ≤ 2^63` (`hvBalance`), implied by its encoding as a signed 64-bit
  integer, the range §4.13 uses. Consensus restricts it further, to `[−MAX_MONEY, MAX_MONEY]`
  (§7.1.2 "Transaction Consensus Rules"); that is not needed here.
-/

namespace Sapling.BindingSignature

/-- The Jubjub scalar order `ℓ`: the order of Jubjub's prime-order subgroup, the spec's `r_𝕁`. An
`abbrev` so that CompElliptic's `Fact (Nat.Prime JUBJUB_SCALAR_CARD)` instance applies to it. -/
abbrev jubjubScalarOrder : ℕ := CompElliptic.Fields.Jubjub.JUBJUB_SCALAR_CARD

/-- `ℓ` is the decimal value the spec gives for `r_𝕁` (§5.4.9.3 "Jubjub"). -/
example : jubjubScalarOrder =
    6554484396890773809930967563523245729705921265872317281365359162392183254199 := rfl

/-- `ℓ` is prime, by CompElliptic's Pratt certificate. -/
example : Fact (Nat.Prime jubjubScalarOrder) := inferInstance

/-- Jubjub's cofactor `8` is nonzero mod `ℓ`, so `eq_of_nsmul_map_eq` can cancel it. -/
theorem eight_ne_zero_jubjub : (8 : ZMod jubjubScalarOrder) ≠ 0 := by decide

/-! ### Description sizes and counts -/

/-- The maximum transaction size: a transaction must fit in a block, and a block is at most
`2000000` bytes (§7.6 "Block Header Encoding and Consensus"; §4.13 uses this limit). -/
def maxTxBytes : ℕ := 2000000

/-- The bytes of a Sapling spend in a version 4 transaction (§7.3 "Spend Description Encoding and
Consensus"). -/
def saplingSpendBytesV4 : ℕ :=
  32 +    -- cv
  32 +    -- anchor (per spend in version 4)
  32 +    -- nullifier
  32 +    -- rk
  192 +   -- zkproof
  64      -- spendAuthSig

/-- The bytes a Sapling spend contributes to a version 5 or 6 transaction. The anchor is shared
across the transaction; the proof and signature move to per-spend arrays (`vSpendProofsSapling`,
`vSpendAuthSigs`) but are still counted once per spend (§7.1 "Transaction Encoding and
Consensus"). That format table covers versions 5 and 6. -/
def saplingSpendBytesV5 : ℕ :=
  32 +    -- cv
  32 +    -- nullifier
  32 +    -- rk
  192 +   -- zkproof      (in vSpendProofsSapling)
  64      -- spendAuthSig (in vSpendAuthSigs)

/-- The minimum bytes of a Sapling spend over all transaction versions. -/
def saplingMinSpendBytes : ℕ := min saplingSpendBytesV4 saplingSpendBytesV5

/-- The bytes of a Sapling output in any transaction version (§7.4 "Output Description Encoding and
Consensus"). In versions 5 and 6 the proof moves to `vOutputProofsSapling` but is still counted
once per output. -/
def saplingOutputBytes : ℕ :=
  32 +    -- cv
  32 +    -- cmu
  32 +    -- ephemeralKey
  580 +   -- encCiphertext
  80 +    -- outCiphertext
  192     -- zkproof

/-- The maximum number of spends in a transaction. -/
def saplingMaxSpends : ℕ := maxTxBytes / saplingMinSpendBytes

/-- The maximum number of outputs in a transaction. -/
def saplingMaxOutputs : ℕ := maxTxBytes / saplingOutputBytes

-- The values §4.13 states: 352 bytes per spend and 948 per output, so at most 5681 spends and
-- 2109 outputs (its pre-NU5 edition gives 384 bytes and 5208 spends for version 4). The version 4
-- count is below the overall maximum, so `saplingMaxSpends` covers every version.
example : saplingSpendBytesV4 = 384 := rfl
example : saplingMinSpendBytes = 352 := rfl
example : saplingOutputBytes = 948 := rfl
example : maxTxBytes / saplingSpendBytesV4 = 5208 := rfl
example : saplingMaxSpends = 5681 := rfl
example : saplingMaxOutputs = 2109 := rfl

/-- `n` spends of at least `saplingMinSpendBytes` bytes fit in `maxTxBytes` only if
`n ≤ saplingMaxSpends`. -/
theorem sapling_spend_count (n : ℕ) (h : saplingMinSpendBytes * n ≤ maxTxBytes) :
    n ≤ saplingMaxSpends := by
  simp only [saplingMaxSpends, maxTxBytes, show saplingMinSpendBytes = 352 from rfl] at h ⊢
  omega

/-- `m` outputs of `saplingOutputBytes` bytes fit in `maxTxBytes` only if
`m ≤ saplingMaxOutputs`. -/
theorem sapling_output_count (m : ℕ) (h : saplingOutputBytes * m ≤ maxTxBytes) :
    m ≤ saplingMaxOutputs := by
  simp only [saplingOutputBytes, saplingMaxOutputs, maxTxBytes] at h ⊢
  omega

/-! ### The bound

Bounding spends and outputs separately is looser than the joint limit
`352 · n + 948 · m ≤ maxTxBytes`, and the resulting symmetric bound on the net value is looser than
the spec's asymmetric range for it; both only enlarge the bound, which is sound. From NU5 onward a
separate consensus rule also caps each count below `2^16`, in every transaction version (§7.1.2
"Transaction Consensus Rules"); it is not used here, because it does not hold for transactions
mined before NU5. -/

/-- The Sapling net-value magnitude bound, `vSumBound (saplingMaxSpends + saplingMaxOutputs)`. -/
def saplingVSumBound : ℤ := vSumBound (saplingMaxSpends + saplingMaxOutputs)

/-- `saplingVSumBound` in closed form: `(5681 + 2109) · (2^64 − 1) + 2^63`. -/
theorem saplingVSumBound_eq : saplingVSumBound = (5681 + 2109) * (2^64 - 1) + 2^63 := by
  simp only [saplingVSumBound, vSumBound, show saplingMaxSpends = 5681 from rfl,
    show saplingMaxOutputs = 2109 from rfl]
  norm_num

/-- The range §4.13 states for the net value in a version 5 transaction,
`[−38913406623490299131842, 104805176454780817500623]`, lies within `saplingVSumBound`. -/
example : (104805176454780817500623 : ℤ) ≤ saplingVSumBound ∧
    (38913406623490299131842 : ℤ) ≤ saplingVSumBound := by
  rw [saplingVSumBound_eq]; norm_num

/-- **Sapling no-overflow bound.** Spend values `olds` and output values `news`, each in
`[0, 2^64 − 1]`, at most `saplingMaxSpends` and `saplingMaxOutputs` of them, and
`|vBalance| ≤ 2^63`, give `(olds.sum − news.sum − vBalance).natAbs < r` once
`saplingVSumBound < r`. The spends followed by the negated outputs form one list of values of
magnitude `≤ 2^64 − 1`, to which `natAbs_lt_of_vSumBound` applies. -/
theorem sapling_natAbs_lt {r : ℕ} (olds news : List ℤ) (vBalance : ℤ)
    (hOld : ∀ v ∈ olds, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ news, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hnOld : olds.length ≤ saplingMaxSpends)
    (hnNew : news.length ≤ saplingMaxOutputs)
    (hvBalance : |vBalance| ≤ 2^63)
    (hr : saplingVSumBound < (r : ℤ)) :
    (olds.sum - news.sum - vBalance).natAbs < r := by
  have hmapneg : (news.map Neg.neg).sum = -news.sum := by simp [List.sum_neg]
  have hv : ∀ v ∈ olds ++ news.map Neg.neg, |v| ≤ 2^64 - 1 := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact abs_le.mpr ⟨by linarith [(hOld v h).1, show (0:ℤ) ≤ 2^64 - 1 by norm_num], (hOld v h).2⟩
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
      exact abs_le.mpr
        ⟨by linarith [(hNew w hw).2],
          by linarith [(hNew w hw).1, show (0:ℤ) ≤ 2^64 - 1 by norm_num]⟩
  have hlen : (olds ++ news.map Neg.neg).length ≤ saplingMaxSpends + saplingMaxOutputs := by
    rw [List.length_append, List.length_map]; exact Nat.add_le_add hnOld hnNew
  have key := natAbs_lt_of_vSumBound (olds ++ news.map Neg.neg) vBalance
    (saplingMaxSpends + saplingMaxOutputs) hv hlen hvBalance hr
  rwa [List.sum_append, hmapneg, ← sub_eq_add_neg] at key

/-- The Sapling no-overflow bound from byte budgets: with the value and balance ranges of
`sapling_natAbs_lt`, spends and outputs that fit in `maxTxBytes` give
`(olds.sum − news.sum − vBalance).natAbs < r` once `saplingVSumBound < r`. The counts come from
`sapling_spend_count` and `sapling_output_count`. -/
theorem sapling_natAbs_lt_of_bytes {r : ℕ} (olds news : List ℤ) (vBalance : ℤ)
    (hOld : ∀ v ∈ olds, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ news, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hSpend : saplingMinSpendBytes * olds.length ≤ maxTxBytes)
    (hOutput : saplingOutputBytes * news.length ≤ maxTxBytes)
    (hvBalance : |vBalance| ≤ 2^63)
    (hr : saplingVSumBound < (r : ℤ)) :
    (olds.sum - news.sum - vBalance).natAbs < r :=
  sapling_natAbs_lt olds news vBalance hOld hNew
    (sapling_spend_count _ hSpend) (sapling_output_count _ hOutput) hvBalance hr

/-- The bound fits the Jubjub scalar field: `saplingVSumBound < ℓ`, the `hr` that instantiates the
bounds above at `r = ℓ`. -/
theorem saplingVSumBound_lt_jubjubScalarOrder : saplingVSumBound < (jubjubScalarOrder : ℤ) := by
  rw [saplingVSumBound_eq]; norm_num [jubjubScalarOrder]

/-! ### The Sapling reduction -/

/-- **Sapling balance reduction (integer level).** A bundle whose spend and output values lie in
`[0, 2^64 − 1]` (`hOld`, `hNew`) and fit the byte budgets (`hSpend`, `hOutput`), with
`|vBalance| ≤ 2^63` (`hvBalance`), a nonzero integer net value (`hne`), and a key `bsk'` with
`bindingVK … = bsk' • Rbase` (`hExtract`), yields a nontrivial relation between `Vbase` and `Rbase`.
It is `NontrivialRelation.ofBundleIntImbalance` at `r = ℓ`, with `hbound` from
`sapling_natAbs_lt_of_bytes`. `hExtract` is the exact form; `NontrivialRelation.ofSaplingBundle`
takes the cofactored one on the full curve, which extraction from deployed verification gives. -/
def NontrivialRelation.ofSaplingImbalance {M : Type*} [AddCommGroup M]
    [Module (ZMod jubjubScalarOrder) M]
    (Vbase Rbase : M) (spends outputs : List (ℤ × ZMod jubjubScalarOrder)) (vBalance : ℤ)
    (bsk' : ZMod jubjubScalarOrder)
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hOld : ∀ v ∈ spends.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ outputs.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hSpend : saplingMinSpendBytes * spends.length ≤ maxTxBytes)
    (hOutput : saplingOutputBytes * outputs.length ≤ maxTxBytes)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK Vbase Rbase (castBundle spends) (castBundle outputs)
      (vBalance : ZMod jubjubScalarOrder) = bsk' • Rbase) :
    NontrivialRelation (F := ZMod jubjubScalarOrder) Vbase Rbase :=
  NontrivialRelation.ofBundleIntImbalance Vbase Rbase spends outputs vBalance bsk' hne
    (sapling_natAbs_lt_of_bytes (spends.map Prod.fst) (outputs.map Prod.fst) vBalance hOld hNew
      (by rwa [List.length_map]) (by rwa [List.length_map]) hvBalance
      saplingVSumBound_lt_jubjubScalarOrder)
    hExtract

/-- The hypotheses of `NontrivialRelation.ofSaplingImbalance` hold together: in `ZMod ℓ` with
`Vbase = Rbase = 1`, one spend of value `1`, no outputs, `vBalance = 0` and `bsk' = 1`, it returns
the relation with coefficients `(1, −1)`. This shows non-vacuity only, nothing about Jubjub. -/
example :
    let rel := NontrivialRelation.ofSaplingImbalance (1 : ZMod jubjubScalarOrder) 1 [(1, 0)] [] 0 1
      (by decide) (by simp) (by simp) (by decide) (by decide) (by norm_num)
      (by simp [bindingVK, castBundle, valueCommit])
    rel.α = 1 ∧ rel.β = -1 :=
  ⟨rfl, rfl⟩

/-- A Sapling bundle with nonzero integer net value (`hne`), whose key as the verifier computes it
satisfies the cofactored `8 • verifierBVK … = 8 • ι (bsk' • Rbase)` (`hExtract8`), yields a
nontrivial relation between `Vbase` and `Rbase`, given the ranges and byte budgets of
`NontrivialRelation.ofSaplingImbalance` (`hOld`, `hNew`, `hSpend`, `hOutput`, `hvBalance`). The
openings (`hcvIn`, `hcvOut`) put that key in the image of the injective `ι`, where `8` cancels. -/
def NontrivialRelation.ofSaplingBundle {M G : Type*} [AddCommGroup M]
    [Module (ZMod jubjubScalarOrder) M] [AddCommGroup G] (ι : M →+ G) (hι : Function.Injective ι)
    (Vbase Rbase : M) (spends outputs : List (ℤ × ZMod jubjubScalarOrder)) (cvIn cvOut : List G)
    (vBalance : ℤ) (bsk' : ZMod jubjubScalarOrder)
    (hcvIn : cvIn = spends.map fun p =>
      ι (valueCommit Vbase Rbase (p.1 : ZMod jubjubScalarOrder) p.2))
    (hcvOut : cvOut = outputs.map fun p =>
      ι (valueCommit Vbase Rbase (p.1 : ZMod jubjubScalarOrder) p.2))
    (hne : (spends.map Prod.fst).sum - (outputs.map Prod.fst).sum - vBalance ≠ 0)
    (hOld : ∀ v ∈ spends.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hNew : ∀ v ∈ outputs.map Prod.fst, 0 ≤ v ∧ v ≤ 2^64 - 1)
    (hSpend : saplingMinSpendBytes * spends.length ≤ maxTxBytes)
    (hOutput : saplingOutputBytes * outputs.length ≤ maxTxBytes)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract8 : 8 • verifierBVK (ι Vbase) cvIn cvOut vBalance = 8 • ι (bsk' • Rbase)) :
    NontrivialRelation (F := ZMod jubjubScalarOrder) Vbase Rbase :=
  NontrivialRelation.ofSaplingImbalance Vbase Rbase spends outputs vBalance bsk' hne hOld hNew
    hSpend hOutput hvBalance (eq_of_nsmul_map_eq ι hι eight_ne_zero_jubjub (by
      subst hcvIn hcvOut; rwa [verifierBVK_of_openings] at hExtract8))

/-- The hypotheses of `NontrivialRelation.ofSaplingBundle` hold together: with `M = G = ZMod ℓ`
and `ι` the identity, `Vbase = Rbase = 1`, one spend of value `1` committed as `1`, no outputs,
`vBalance = 0` and `bsk' = 1`, it returns the relation with coefficients `(1, −1)`. This shows
non-vacuity only, nothing about Jubjub. -/
example :
    let rel := NontrivialRelation.ofSaplingBundle (AddMonoidHom.id (ZMod jubjubScalarOrder))
      Function.injective_id 1 1 [(1, 0)] [] [1] [] 0 1
      (by simp [valueCommit]) rfl (by decide) (by simp) (by simp) (by decide) (by decide)
      (by norm_num) (by simp [verifierBVK])
    rel.α = 1 ∧ rel.β = -1 :=
  ⟨rfl, rfl⟩

end Sapling.BindingSignature
