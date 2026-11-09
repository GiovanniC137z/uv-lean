import UV.WeakProfileBracket
import UV.FormalBRSTTopology

/-! Genuine formal coefficients of weak continuum integrals. Continuous
coefficient maps commute with the actual represented weak integral. The
signed variational bracket is expanded by the finite Cauchy convolution;
no separate convergence of its potentially grouped constituent products
is imposed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators PowerSeries.WithPiTopology

namespace UV

section Coefficients

variable {X A : Type*} [MeasurableSpace X] [Ring A] [Algebra ℝ A]
  [TopologicalSpace A] {μ : Measure X}

/-- The genuine nth coefficient is a continuous real linear map for the
actual product topology on formal power series. -/
def powerSeriesCoeffCLM (n : ℕ) : PowerSeries A →L[ℝ] A where
  toFun := PowerSeries.coeff n
  map_add' f g := map_add _ f g
  map_smul' r f := PowerSeries.coeff_smul n f r
  cont := PowerSeries.WithPiTopology.continuous_coeff A n

@[simp] theorem powerSeriesCoeffCLM_apply (n : ℕ) (f : PowerSeries A) :
    powerSeriesCoeffCLM n f = PowerSeries.coeff n f := rfl

theorem WeakIntegrable.formalCoeff {f : X → PowerSeries A}
    (hf : WeakIntegrable μ f) (n : ℕ) :
    WeakIntegrable μ (fun x => PowerSeries.coeff n (f x)) :=
  hf.map (powerSeriesCoeffCLM n)

/-- The actual weak integral, rather than a separately postulated series
of integrals, determines every formal coefficient. -/
theorem weakIntegral_formalCoeff [SeparatingDual ℝ A] {f : X → PowerSeries A}
    (n : ℕ) (hf : WeakIntegrable μ f) :
    PowerSeries.coeff n (weakIntegral μ f) =
      weakIntegral μ (fun x => PowerSeries.coeff n (f x)) :=
  (weakIntegral_map (powerSeriesCoeffCLM n) hf).symm

omit [Algebra ℝ A] [TopologicalSpace A] in
theorem powerSeries_coeff_mul_range (F H : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (F*H) = ∑ j ∈ Finset.range (n+1),
      PowerSeries.coeff j F * PowerSeries.coeff (n-j) H := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ n

theorem weakIntegral_formal_product_coeff [SeparatingDual ℝ A]
    {F H : X → PowerSeries A} (n : ℕ)
    (hI : WeakIntegrable μ (fun x => F x * H x))
    (hcoeff : ∀ j ∈ Finset.range (n+1), WeakIntegrable μ
      (fun x => PowerSeries.coeff j (F x) * PowerSeries.coeff (n-j) (H x))) :
    PowerSeries.coeff n (weakIntegral μ (fun x => F x * H x)) =
      ∑ j ∈ Finset.range (n+1), weakIntegral μ
        (fun x => PowerSeries.coeff j (F x) * PowerSeries.coeff (n-j) (H x)) := by
  rw [weakIntegral_formalCoeff n hI]
  simp_rw [powerSeries_coeff_mul_range]
  exact weakIntegral_finset_sum _ _ hcoeff

end Coefficients

section SignedPairs

variable {X A : Type*} [MeasurableSpace X] [Ring A] [Algebra ℚ A] [Algebra ℝ A]
  [TopologicalSpace A] {μ : Measure X}

omit [Algebra ℝ A] [TopologicalSpace A] in
theorem formalProfilePair_coeff (σ : GradingInvolution A) (p : Bool)
    (R L R' L' : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (weakProfilePair (formalGrading σ) p R L R' L') =
      ∑ j ∈ Finset.range (n+1), weakProfilePair σ p
        (PowerSeries.coeff j R) (PowerSeries.coeff j L)
        (PowerSeries.coeff (n-j) R') (PowerSeries.coeff (n-j) L') := by
  cases p <;> simp only [weakProfilePair, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true, map_sub, powerSeries_coeff_mul_range,
    formalGrading_coeff, Finset.sum_sub_distrib]

/-- The combined signed bracket is the integrable object throughout this
identity. Individual constituent products need not have separate integrals. -/
theorem weakIntegral_formal_profilePair_coeff [SeparatingDual ℝ A]
    (σ : GradingInvolution A) (ε : X → Bool)
    (R L R' L' : X → PowerSeries A) (n : ℕ)
    (hI : WeakIntegrable μ (fun x => weakProfilePair (formalGrading σ) (ε x)
      (R x) (L x) (R' x) (L' x)))
    (hcoeff : ∀ j ∈ Finset.range (n+1), WeakIntegrable μ
      (fun x => weakProfilePair σ (ε x)
        (PowerSeries.coeff j (R x)) (PowerSeries.coeff j (L x))
        (PowerSeries.coeff (n-j) (R' x)) (PowerSeries.coeff (n-j) (L' x)))) :
    PowerSeries.coeff n (weakIntegral μ (fun x => weakProfilePair (formalGrading σ) (ε x)
      (R x) (L x) (R' x) (L' x))) =
      ∑ j ∈ Finset.range (n+1), weakIntegral μ
        (fun x => weakProfilePair σ (ε x)
          (PowerSeries.coeff j (R x)) (PowerSeries.coeff j (L x))
          (PowerSeries.coeff (n-j) (R' x)) (PowerSeries.coeff (n-j) (L' x))) := by
  rw [weakIntegral_formalCoeff n hI]
  simp_rw [formalProfilePair_coeff]
  exact weakIntegral_finset_sum _ _ hcoeff

end SignedPairs

section RegularProfiles

variable {X A B : Type*} [MeasurableSpace X]
  [Ring A] [Algebra ℚ A] [Algebra ℝ A] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [Ring B] [Algebra ℚ B] [Algebra ℝ B] [TopologicalSpace B]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B]
  {μ : Measure X} {σA : GradingInvolution A} {σB : GradingInvolution B}
  {ε : X → Bool} {W : A} {G : Type*} {T : Bool → Type*}
  {c : WeakContinuumLegendreDomain μ σA σB ε W G T} {U : Subalgebra ℚ B}

def weakFormalRightProfile (v : WeakRegularGradientCalculus c U)
    (F : PowerSeries U) (x : X) : PowerSeries B :=
  PowerSeries.mk (fun n => v.rightField (PowerSeries.coeff n F) x)

def weakFormalLeftProfile (v : WeakRegularGradientCalculus c U)
    (F : PowerSeries U) (x : X) : PowerSeries B :=
  PowerSeries.mk (fun n => v.leftAntifield (PowerSeries.coeff n F) x)

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
@[simp] theorem weakFormalRightProfile_coeff (v : WeakRegularGradientCalculus c U)
    (F : PowerSeries U) (x : X) (n : ℕ) :
    PowerSeries.coeff n (weakFormalRightProfile v F x) =
      v.rightField (PowerSeries.coeff n F) x := by
  simp [weakFormalRightProfile]

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [IsTopologicalRing B] [ContinuousSMul ℝ B] [T2Space B] [SeparatingDual ℝ B] in
@[simp] theorem weakFormalLeftProfile_coeff (v : WeakRegularGradientCalculus c U)
    (F : PowerSeries U) (x : X) (n : ℕ) :
    PowerSeries.coeff n (weakFormalLeftProfile v F x) =
      v.leftAntifield (PowerSeries.coeff n F) x := by
  simp [weakFormalLeftProfile]

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [ContinuousSMul ℝ B] [T2Space B] in
/-- The actual weak-integral bracket of formal variational profiles has
the Cauchy coefficients of the genuine regular-domain bracket. -/
theorem weakFormalRegularBracket_coeff (v : WeakRegularGradientCalculus c U)
    (F H : PowerSeries U)
    (hI : WeakIntegrable μ (fun x => weakProfilePair (formalGrading σB) (ε x)
      (weakFormalRightProfile v F x) (weakFormalLeftProfile v F x)
      (weakFormalRightProfile v H x) (weakFormalLeftProfile v H x))) (n : ℕ) :
    PowerSeries.coeff n (weakIntegral μ (fun x => weakProfilePair (formalGrading σB) (ε x)
      (weakFormalRightProfile v F x) (weakFormalLeftProfile v F x)
      (weakFormalRightProfile v H x) (weakFormalLeftProfile v H x))) =
      ∑ j ∈ Finset.range (n+1),
        (weakRegularBracket v (PowerSeries.coeff j F) (PowerSeries.coeff (n-j) H) : B) := by
  rw [weakIntegral_formal_profilePair_coeff σB ε _ _ _ _ n hI]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [weakFormalRightProfile_coeff, weakFormalLeftProfile_coeff]
    rfl
  · intro j _
    simpa only [weakFormalRightProfile_coeff, weakFormalLeftProfile_coeff] using
      v.bracket_integrable (PowerSeries.coeff j F) (PowerSeries.coeff (n-j) H)

omit [IsTopologicalRing A] [ContinuousSMul ℝ A] [T2Space A] [SeparatingDual ℝ A]
  [ContinuousSMul ℝ B] [T2Space B] in
/-- Identification of the whole formal bracket, not merely an arbitrary
linear projection. The right side uses the previously constructed actual
weak-integral regular bracket. -/
theorem weakFormalRegularBracket_eq (v : WeakRegularGradientCalculus c U)
    (F H : PowerSeries U)
    (hI : WeakIntegrable μ (fun x => weakProfilePair (formalGrading σB) (ε x)
      (weakFormalRightProfile v F x) (weakFormalLeftProfile v F x)
      (weakFormalRightProfile v H x) (weakFormalLeftProfile v H x))) :
    weakIntegral μ (fun x => weakProfilePair (formalGrading σB) (ε x)
      (weakFormalRightProfile v F x) (weakFormalLeftProfile v F x)
      (weakFormalRightProfile v H x) (weakFormalLeftProfile v H x)) =
      PowerSeries.map U.val.toRingHom (formalBilinear (weakRegularBracket v) F H) := by
  ext n
  rw [weakFormalRegularBracket_coeff v F H hI n, PowerSeries.coeff_map,
    formalBilinear_coeff_range, map_sum]
  rfl

end RegularProfiles

end UV
