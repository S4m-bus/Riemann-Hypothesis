import RiemannHypothesis.AdelicFlow.G4TransverseQuotient

noncomputable section

namespace RiemannHypothesis.AdelicFlow

/-!
# G4: normalized archimedean slice and the global-flow bridge

We now connect the finite transverse quotient back to the actual twice-quotient
scaling-site flow.  Use the normalized pre-quotient slice

    y ↦ (1, y) ∈ A_∞ × A_f.

At time `-m log p`, the archimedean flow multiplies the first coordinate by
`p^{-m}`.  Principal multiplication by `p^m` restores that coordinate to 1 and
acts on the finite coordinate by the stable transverse return.  Since principal
rational scaling is already killed in the scaling-site quotient, the global
flow at negative prime time is intertwined with the stable transverse quotient
return.

This is a genuine quotient-flow compatibility theorem.  It still does not prove
G3 orbit exhaustion or injectivity of the slice map.
-/

/-- The canonical class map from the exposed global carrier to the twice
quotiented scaling site. -/
def scalingSiteClass (a : GlobalSpace) : ScalingSiteQuotient :=
  toScalingSiteQuotient (toPrincipalQuotient a)

/-- The normalized archimedean slice of the pre-quotient global adele carrier. -/
def normalizedArchimedeanSlice
    (y : PrequotientTransverseCarrier) : GlobalSpace :=
  (1, y)

@[simp]
theorem transverseProjection_normalizedArchimedeanSlice
    (y : PrequotientTransverseCarrier) :
    transverseProjection (normalizedArchimedeanSlice y) = y := rfl

/-- The stable corrected return restores the normalized archimedean slice and
acts on its finite coordinate by the stable transverse return. -/
theorem stableCorrectedGlobalReturn_on_normalizedSlice
    (p m : ℕ) (hp : Nat.Prime p)
    (y : PrequotientTransverseCarrier) :
    stableCorrectedGlobalReturn p m hp (normalizedArchimedeanSlice y) =
      normalizedArchimedeanSlice (stableTransverseReturn p m hp y) := by
  apply Prod.ext
  · funext v
    have hpR : ((p : ℝ) ^ m) ≠ 0 := by
      exact pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    simp only [stableCorrectedGlobalReturn, normalizedArchimedeanSlice,
      globalScale, infiniteScale, archimedeanGlobalFlow,
      rationalInfiniteRealFlow, primePowerUnit,
      NumberField.InfiniteAdeleRing.algebraMap_apply, mul_one]
    change ((p : v.Completion) ^ m) *
        (ratRealCoordinate v).symm (Real.exp (negativePrimeReturnTime p m)) = 1
    apply (ratRealCoordinate v).injective
    rw [map_mul, map_pow, map_natCast]
    simp only [RingEquiv.apply_symm_apply, map_one]
    rw [exp_negativePrimeReturnTime p m hp]
    exact mul_inv_cancel₀ hpR
  · rfl

/-- Principal rational scaling does not change a scaling-site class. -/
theorem scalingSiteClass_principalScale
    (u : ℚˣ) (a : GlobalSpace) :
    scalingSiteClass (globalScale u a) = scalingSiteClass a := by
  unfold scalingSiteClass
  exact congrArg toScalingSiteQuotient
    (principal_scale_trivial_on_quotient u a)

/-- Maximal-compact finite scaling does not change a scaling-site class. -/
theorem scalingSiteClass_compactGlobalScale
    (k : MaxCompactFiniteUnit) (a : GlobalSpace) :
    scalingSiteClass (compactGlobalScale k a) = scalingSiteClass a := by
  unfold scalingSiteClass
  rw [← principalCompactScale_mk]
  exact compact_scale_trivial_on_scalingSite k (toPrincipalQuotient a)

/-- A finite transverse representative determines a scaling-site class through
the normalized archimedean slice. -/
def finiteSliceClass
    (y : PrequotientTransverseCarrier) : ScalingSiteQuotient :=
  scalingSiteClass (normalizedArchimedeanSlice y)

/-- The normalized-slice class is invariant under compact finite scaling. -/
theorem finiteSliceClass_respects_compact
    {x y : PrequotientTransverseCarrier}
    (hxy : FiniteCompactEquivalent x y) :
    finiteSliceClass x = finiteSliceClass y := by
  rcases hxy with ⟨k, hk⟩
  rw [← hk]
  change scalingSiteClass (normalizedArchimedeanSlice x) =
    scalingSiteClass (normalizedArchimedeanSlice (compactFiniteScale k x))
  have hglobal :
      compactGlobalScale k (normalizedArchimedeanSlice x) =
        normalizedArchimedeanSlice (compactFiniteScale k x) := rfl
  rw [← hglobal, scalingSiteClass_compactGlobalScale]

/-- The normalized finite slice descends through `A_f / K_f` into the actual
scaling-site quotient.  No injectivity is claimed here. -/
def finiteTransverseSliceMap :
    FiniteTransverseQuotient → ScalingSiteQuotient :=
  Quotient.lift finiteSliceClass
    (by
      intro x y hxy
      exact finiteSliceClass_respects_compact hxy)

@[simp]
theorem finiteTransverseSliceMap_mk
    (y : PrequotientTransverseCarrier) :
    finiteTransverseSliceMap (toFiniteTransverseQuotient y) =
      finiteSliceClass y := rfl

/-- On normalized representatives, the actual scaling-site flow at negative
prime time agrees with the stable transverse return. -/
theorem scalingSiteFlow_negativePrimeTime_finiteSlice
    (p m : ℕ) (hp : Nat.Prime p)
    (y : PrequotientTransverseCarrier) :
    scalingSiteFlow (negativePrimeReturnTime p m) (finiteSliceClass y) =
      finiteSliceClass (stableTransverseReturn p m hp y) := by
  change scalingSiteClass
      (archimedeanGlobalFlow (negativePrimeReturnTime p m)
        (normalizedArchimedeanSlice y)) =
    scalingSiteClass
      (normalizedArchimedeanSlice (stableTransverseReturn p m hp y))
  calc
    scalingSiteClass
        (archimedeanGlobalFlow (negativePrimeReturnTime p m)
          (normalizedArchimedeanSlice y)) =
      scalingSiteClass
        (globalScale (primePowerUnit p m hp)
          (archimedeanGlobalFlow (negativePrimeReturnTime p m)
            (normalizedArchimedeanSlice y))) :=
      (scalingSiteClass_principalScale
        (primePowerUnit p m hp)
        (archimedeanGlobalFlow (negativePrimeReturnTime p m)
          (normalizedArchimedeanSlice y))).symm
    _ = scalingSiteClass
        (normalizedArchimedeanSlice (stableTransverseReturn p m hp y)) := by
      rw [show
        globalScale (primePowerUnit p m hp)
            (archimedeanGlobalFlow (negativePrimeReturnTime p m)
              (normalizedArchimedeanSlice y)) =
          stableCorrectedGlobalReturn p m hp
            (normalizedArchimedeanSlice y) from rfl,
        stableCorrectedGlobalReturn_on_normalizedSlice]

/-- Quotient-level G4 bridge: negative prime-time global scaling is intertwined
with the stable return on the finite arithmetic transverse quotient. -/
theorem finiteTransverseSliceMap_intertwines_stableReturn
    (p m : ℕ) (hp : Nat.Prime p)
    (x : FiniteTransverseQuotient) :
    scalingSiteFlow (negativePrimeReturnTime p m)
      (finiteTransverseSliceMap x) =
    finiteTransverseSliceMap (stableTransverseQuotientReturn p m hp x) := by
  refine Quotient.inductionOn x ?_
  intro y
  exact scalingSiteFlow_negativePrimeTime_finiteSlice p m hp y

end RiemannHypothesis.AdelicFlow
