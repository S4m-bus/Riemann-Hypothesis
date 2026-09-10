import RiemannHypothesis.AdelicFlow.G4ReturnModulus
import RiemannHypothesis.AdelicFlow.ArchimedeanFlow

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G4: transverse geometry of the scaling orbit

The exposed rational adele carrier is literally a product

    A_∞ × A_f.

The archimedean real flow acts only on the first factor.  Therefore the finite
factor is a canonical pre-quotient transversal to the real scaling direction:
its coordinate is unchanged by pure archimedean flow.  This file formalizes
that splitting and combines it with the already kernel-checked finite return
modulus.

Important orientation convention: the quantity used here is the contracting
(stable) transverse modulus.  The unrestricted full adelic modulus is still 1
by the product formula; the finite/stable transverse modulus is p^{-m}.
-/

/-- The canonical finite transverse carrier in the exposed product model. -/
abbrev PrequotientTransverseCarrier : Type := RationalFiniteAdele

/-- Projection to the finite transverse coordinate. -/
def transverseProjection (a : GlobalSpace) : PrequotientTransverseCarrier := a.2

/-- Inclusion of a finite transverse vector at zero archimedean coordinate. -/
def transverseInclusion (y : PrequotientTransverseCarrier) : GlobalSpace := (0, y)

@[simp]
theorem transverseProjection_inclusion (y : PrequotientTransverseCarrier) :
    transverseProjection (transverseInclusion y) = y := rfl

/-- Pure archimedean flow leaves the finite transverse coordinate exactly
unchanged.  This is the product-splitting content behind `J_∞^⊥ = 1`. -/
theorem transverseProjection_archimedeanFlow
    (t : ℝ) (a : GlobalSpace) :
    transverseProjection (archimedeanGlobalFlow t a) = transverseProjection a := rfl

/-- The induced pure archimedean action on the chosen finite transversal. -/
def archimedeanTransverseAction (_t : ℝ)
    (y : PrequotientTransverseCarrier) : PrequotientTransverseCarrier := y

@[simp]
theorem archimedeanTransverseAction_eq_identity
    (t : ℝ) (y : PrequotientTransverseCarrier) :
    archimedeanTransverseAction t y = y := rfl

/-- Modulus of the pure archimedean action on the finite transversal. -/
def archimedeanTransverseModulus (_t : ℝ) : ℚ := 1

@[simp]
theorem archimedeanTransverseModulus_eq_one (t : ℝ) :
    archimedeanTransverseModulus t = 1 := rfl

/-- The stable global transverse return modulus: the orbit-direction
archimedean factor is removed and the finite return modulus remains. -/
def stableGlobalTransverseModulus (p m : ℕ) : ℚ :=
  archimedeanTransverseModulus ((m : ℝ) * Real.log (p : ℝ)) *
    finiteReturnModulus p m

/-- G4 stable-modulus theorem: for a prime `p`, the `m`-fold stable transverse
return modulus is exactly `p^{-m}`. -/
theorem stableGlobalTransverseModulus_eq_inv_pow
    (p m : ℕ) (hp : Nat.Prime p) :
    stableGlobalTransverseModulus p m = ((p : ℚ) ^ m)⁻¹ := by
  simp [stableGlobalTransverseModulus,
    finiteReturnModulus_eq_inv_pow p m hp]

/-- Positive half-density of the stable global transverse modulus. -/
def stableGlobalTransverseHalfDensity (p m : ℕ) : ℝ :=
  Real.sqrt (((p : ℝ) ^ m)⁻¹)

/-- Squaring the stable transverse half-density gives exactly `p^{-m}`. -/
theorem stableGlobalTransverseHalfDensity_sq
    (p m : ℕ) (hp : Nat.Prime p) :
    (stableGlobalTransverseHalfDensity p m) ^ 2 = ((p : ℝ) ^ m)⁻¹ := by
  unfold stableGlobalTransverseHalfDensity
  rw [Real.sq_sqrt]
  positivity

/-- The stable and unrestricted adelic moduli are genuinely different:
full adelic modulus is 1, while the stable transverse modulus is `p^{-m}`. -/
theorem full_vs_stable_transverse_modulus
    (p m : ℕ) (hp : Nat.Prime p) :
    fullAdelicReturnModulus p m = 1 ∧
    stableGlobalTransverseModulus p m = ((p : ℚ) ^ m)⁻¹ := by
  exact ⟨fullAdelicReturnModulus_eq_one p m hp,
    stableGlobalTransverseModulus_eq_inv_pow p m hp⟩

/-- The reciprocal unstable modulus.  This records the orientation dependence
of a Poincare return map versus its inverse without identifying either one with
the full adelic modulus. -/
def unstableGlobalTransverseModulus (p m : ℕ) : ℚ :=
  (stableGlobalTransverseModulus p m)⁻¹

/-- Stable and unstable transverse moduli are reciprocal for prime cycles. -/
theorem stable_mul_unstable_eq_one
    (p m : ℕ) (hp : Nat.Prime p) :
    stableGlobalTransverseModulus p m * unstableGlobalTransverseModulus p m = 1 := by
  have hp0 : ((p : ℚ) ^ m) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  rw [stableGlobalTransverseModulus_eq_inv_pow p m hp]
  simp [unstableGlobalTransverseModulus,
    stableGlobalTransverseModulus_eq_inv_pow p m hp, hp0]

end RiemannHypothesis.AdelicFlow
