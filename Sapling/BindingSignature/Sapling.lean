import CompElliptic.Fields.Jubjub

/-!
# Sapling's no-overflow bound

The Jubjub scalar order `ℓ`, the field order at which Sapling instantiates the no-overflow lift of
spec §4.13 "Balance and Binding Signature (Sapling)", taken from CompElliptic with its
kernel-checked primality certificate.

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

end Sapling.BindingSignature
