import CompElliptic.Fields.Jubjub

/-!
# Sapling's no-overflow bound

The Jubjub scalar order `ℓ` and Sapling's description counts, toward the no-overflow lift of spec
§4.13 "Balance and Binding Signature (Sapling)". The spend and output counts come from the 2 MB
transaction size limit and each description's minimum encoded size, summed field by field from
the spec's encoding tables, with each result tied to the spec's stated value by an `example`.
Version 6 transactions use the version 5 Sapling layout.

Section numbers refer to the NU6.3 edition of the Zcash protocol specification.
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

end Sapling.BindingSignature
