import UV.ContinueCompressedModesRigidity

/-! Extract the one-photon matrix element of the longitudinally conjugated
three-compression operator. A single Fourier source generates all
nonnegative harmonics. Each fixed coefficient of the product uses a
finite Cauchy sum. -/

noncomputable section

open UV.SectorPlane
open scoped RealInnerProductSpace Matrix.Norms.L2Operator

namespace UV

variable {ι : Type*} [Fintype ι]

/-- Fourier coefficients of the scalar gauge multiplier exp(a z) at a
single complexified photon tone z = exp(i Q·x). -/
def compressedGaugeTone (a : ℝ) (n : ℕ) : ℝ := a^n/n.factorial

theorem compressed_gauge_tone_exp (a : ℝ) (z : ℂ) :
    HasSum (fun n : ℕ => (compressedGaugeTone a n : ℂ)*z^n) (Complex.exp (a*z)) := by
  rw [Complex.exp_eq_exp_ℂ]
  convert NormedSpace.expSeries_div_hasSum_exp ℂ ((a:ℂ)*z) using 1
  funext n
  simp [compressedGaugeTone,mul_pow,div_mul_eq_mul_div]

/-- Apply the diagonal inverse charged symbol and the linear transverse
insertion to the positive gauge exponential acting on the incoming
plane wave. The latter insertion transfers exactly one copy of Q. -/
def compressedToneBare (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (p Q x : OSFourSpace) (t : ℝ) (n : ℕ) : DiracMatrix :=
  let a := ⟪Q,x⟫/‖Q‖^2
  let F (k : OSFourSpace) := compressedCliffordVertex (compressedVertexFactor L T ξ k Q • (x-compressedLongitudinal Q x))
  let k (j : ℕ) := p + (j:ℝ) • Q
  compressedGaugeTone (t*a) n • normalDiracSymbol m (k n) ξ +
    match n with
    | 0 => 0
    | j+1 => (t*compressedGaugeTone (t*a) j) • F (k j)

/-- Multiply on the left by the negative gauge exponential. Output n
is the matrix element from p to p+nQ of this single-tone conjugation. -/
def compressedToneConjugated (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (p Q x : OSFourSpace) (t : ℝ) (n : ℕ) : DiracMatrix :=
  ∑ j ∈ Finset.range (n+1), compressedGaugeTone (-t*(⟪Q,x⟫/‖Q‖^2)) j •
    compressedToneBare m L T ξ p Q x t (n-j)

theorem compressed_tone_one_photon (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (p Q x : OSFourSpace) (t : ℝ) :
    compressedToneConjugated m L T ξ p Q x t 1 = t • compressedPhotonVertex L T ξ p Q x := by
  let a := ⟪Q,x⟫/‖Q‖^2
  let X := compressedVertexFactor L T ξ p Q • (x-compressedLongitudinal Q x)
  have hD : normalDiracSymbol m (p+Q) ξ - normalDiracSymbol m p ξ = compressedCliffordVertex Q :=
    by
      change normalDiracSymbol m (p+Q) ξ-normalDiracSymbol m p ξ = Complex.I • diracSlash Q
      simp only [normalDiracSymbol,normalFiveSlash,diracSlash_add,smul_add]
      abel
  have hL : compressedLongitudinal Q x = a • Q := rfl
  change _ = t • compressedCliffordVertex (X+compressedLongitudinal Q x)
  simp only [compressedToneConjugated,Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    compressedGaugeTone,compressedToneBare,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,
    pow_one,Nat.factorial_one,Nat.sub_zero,Nat.sub_self,Nat.cast_zero,one_smul,zero_smul,add_zero,mul_one]
  change (t*a) • normalDiracSymbol m (p+Q) ξ + t • compressedCliffordVertex X +
    (-t*a) • normalDiracSymbol m p ξ = _
  rw [hL,map_add,show compressedCliffordVertex (a • Q) = a • compressedCliffordVertex Q from map_smul _ _ _,←hD]
  simp only [smul_add,smul_sub,smul_smul,neg_mul,neg_smul]
  abel

theorem compressed_conjugation_vertex_derivative (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (p Q : OSFourSpace) (u : UnitVector OSFourSpace) :
    HasDerivAt (fun t : ℝ => compressedToneConjugated m L T ξ p Q u.val t 1)
      (compressedPhotonVertex L T ξ p Q u.val) 0 := by
  simp_rw [compressed_tone_one_photon m L T ξ p Q u.val]
  simpa using (hasDerivAt_id (0:ℝ)).smul_const (compressedPhotonVertex L T ξ p Q u.val)

/-- On the fixed post-locking sector-plane, the same oriented chart is
used for the carrier, the nonzero transfer and the unit polarization.
The fifth coordinate is the original shifted normal-circle mode. -/
theorem SectorPlane.Plane.compressed_first_variation_ward {E : Type*} [Norm E] (diamond : Plane E)
    (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (θ : ℝ) (j : ℤ)
    (p Q : OSFourSpace) (u : UnitVector OSFourSpace) (hQ : Q ≠ 0) :
    let R := diamond.osOrientedChart
    let ξ := normalLegFrequency L θ j
    let G := compressedPhotonVertex L T ξ (R p) (R Q)
    HasDerivAt (fun t : ℝ => compressedToneConjugated m L T ξ (R p) (R Q)
      (wilsonRotateUnit R u).val t 1) (G (wilsonRotateUnit R u).val) 0 ∧
    G (R Q) = normalDiracSymbol m (R (p+Q)) ξ-normalDiracSymbol m (R p) ξ := by
  let R := diamond.osOrientedChart
  let ξ := normalLegFrequency L θ j
  have hR : R Q ≠ 0 := by simpa using hQ
  exact ⟨compressed_conjugation_vertex_derivative m L T ξ (R p) (R Q) (wilsonRotateUnit R u),
    (compressed_vertex_ward m L T ξ (R p) (R Q) hR).2.trans (by rw [map_add])⟩

end UV
