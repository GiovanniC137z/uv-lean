import UV.ContinuationVectorialPole
import UV.CliffordWard
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The relative Wilson chord's continuum tree charge on a fixed sector plane.
The analytic carrier coordinate refers to the plane's assigned unit. The
Euclidean square below is its holomorphic continuation, without conjugation. -/

noncomputable section

open Filter
open scoped Topology RealInnerProductSpace Matrix.Norms.Elementwise

namespace UV.SectorPlane

abbrev ChordMomentum := ℂ × (Fin 3 → ℂ)

def chordSquare (k : ChordMomentum) : ℂ :=
  k.1 ^ 2 + ∑ j, k.2 j ^ 2

def chordGaussian (σ : ℝ) (k : ChordMomentum) : ℂ :=
  Complex.exp (-(σ : ℂ) ^ 2 * chordSquare k)

def chordSymbol (σ : ℝ) (k : ChordMomentum) : ChordMomentum :=
  chordGaussian σ k • k

def chordAxialDerivative (σ : ℝ) (k : ChordMomentum) : ChordMomentum :=
  (chordGaussian σ k * (1 - 2 * (σ : ℂ) ^ 2 * k.1 ^ 2),
    fun j => chordGaussian σ k * (-2 * (σ : ℂ) ^ 2 * k.1 * k.2 j))

theorem chord_gaussian_hasDerivAt (σ : ℝ) (k : ChordMomentum) :
    HasDerivAt (fun z : ℂ => chordGaussian σ (z, k.2))
      (chordGaussian σ k * (-2 * (σ : ℂ) ^ 2 * k.1)) k.1 := by
  have hs := ((hasDerivAt_id k.1).pow 2).add_const (∑ j, k.2 j ^ 2)
  have he := (hs.const_mul (-(σ : ℂ) ^ 2)).cexp
  convert he using 1
  simp only [chordGaussian, chordSquare, Pi.pow_apply, id_eq]
  ring

theorem chord_symbol_axial_hasDerivAt (σ : ℝ) (k : ChordMomentum) :
    HasDerivAt (fun z : ℂ => (chordSymbol σ (z, k.2)).1)
      (chordAxialDerivative σ k).1 k.1 := by
  have hh := (chord_gaussian_hasDerivAt σ k).mul (hasDerivAt_id k.1)
  convert hh using 1
  simp only [chordAxialDerivative, id_eq]
  ring

theorem chord_symbol_spatial_hasDerivAt (σ : ℝ) (k : ChordMomentum) (j : Fin 3) :
    HasDerivAt (fun z : ℂ => (chordSymbol σ (z, k.2)).2 j)
      ((chordAxialDerivative σ k).2 j) k.1 := by
  have hh := (chord_gaussian_hasDerivAt σ k).mul_const (k.2 j)
  convert hh using 1
  simp only [chordAxialDerivative]
  ring

theorem chord_gaussian_entire (σ : ℝ) (k : ChordMomentum) :
    AnalyticAt ℂ (chordGaussian σ) k := by
  have h₁ := (ContinuousLinearMap.fst ℂ ℂ (Fin 3 → ℂ)).analyticAt k
  have h₂ : AnalyticAt ℂ (fun k : ChordMomentum => ∑ j, k.2 j ^ 2) k := by
    apply Finset.analyticAt_fun_sum
    intro j _
    exact ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin 3 → ℂ))).analyticAt k |>.pow 2
  exact (analyticAt_const.mul ((h₁.pow 2).add h₂)).cexp'

theorem chord_symbol_entire (σ : ℝ) (k : ChordMomentum) :
    AnalyticAt ℂ (chordSymbol σ) k :=
  (chord_gaussian_entire σ k).smul analyticAt_id

/-- The analytic rest momentum in the chart of the unit carrier. -/
def chordRest (m : ℝ) : ChordMomentum :=
  (Complex.I * (m : ℂ), 0)

theorem chord_rest_square (m : ℝ) : chordSquare (chordRest m) = -(m : ℂ) ^ 2 := by
  simp [chordSquare, chordRest, mul_pow, Complex.I_sq]

theorem Plane.chord_rest_uses_unit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (diamond : Plane E) (m : ℝ) :
    let pGT := m • (diamond.poleUnit : E)
    ⟪(diamond.poleUnit : E), pGT⟫ = m ∧ diamond.transverse pGT = 0 := by
  dsimp [Plane.poleUnit]
  rw [real_inner_smul_right, diamond.inner_carrier_self, mul_one]
  exact ⟨rfl, (diamond.alignment_iff _).mpr ⟨m, rfl⟩⟩

def chordChargeFactor (x : ℝ) : ℝ :=
  Real.exp x * (1 + 2 * x)

theorem chord_charge_factor_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < chordChargeFactor x := by
  unfold chordChargeFactor
  positivity

theorem chord_axial_derivative_at_rest (m σ : ℝ) :
    chordAxialDerivative σ (chordRest m) =
      ((chordChargeFactor (m ^ 2 * σ ^ 2) : ℂ), 0) := by
  apply Prod.ext
  · change chordGaussian σ (chordRest m) * (1 - 2 * (σ : ℂ) ^ 2 * (chordRest m).1 ^ 2) = _
    rw [chordGaussian, chord_rest_square]
    simp only [chordRest, mul_pow, Complex.I_sq, chordChargeFactor, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_pow,
      Complex.ofReal_exp]
    congr 1 <;> ring_nf
  · funext j
    simp [chordAxialDerivative, chordRest]

def chordGammaParallel : DiracMatrix := euclideanGamma 0

def chordRestProjector : DiracMatrix :=
  (1 / 2 : ℂ) • (1 + chordGammaParallel)

theorem chord_gamma_parallel_sq : chordGammaParallel * chordGammaParallel = 1 := by
  have h := euclideanGamma_clifford 0 0
  rw [if_pos rfl] at h
  apply (smul_right_injective DiracMatrix (by norm_num : (2 : ℂ) ≠ 0))
  simpa [chordGammaParallel, two_smul] using h

theorem chord_gamma_mul_rest_projector :
    chordGammaParallel * chordRestProjector = chordRestProjector := by
  rw [chordRestProjector, Matrix.mul_smul, mul_add, mul_one, chord_gamma_parallel_sq,
    add_comm chordGammaParallel]

theorem chord_rest_projector_idempotent :
    chordRestProjector * chordRestProjector = chordRestProjector := by
  calc
    chordRestProjector * chordRestProjector =
        (1 / 2 : ℂ) • (chordRestProjector + chordRestProjector) := by
          rw [chordRestProjector, Matrix.smul_mul, add_mul, one_mul,
            ← chordRestProjector, chord_gamma_mul_rest_projector]
    _ = chordRestProjector := by rw [← two_smul ℂ, smul_smul]; norm_num

theorem chord_rest_projector_gamma :
    chordRestProjector * chordGammaParallel * chordRestProjector = chordRestProjector := by
  rw [mul_assoc, chord_gamma_mul_rest_projector, chord_rest_projector_idempotent]

theorem chord_rest_projector_isHermitian : Matrix.IsHermitian chordRestProjector := by
  unfold Matrix.IsHermitian chordRestProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    show Matrix.conjTranspose chordGammaParallel = chordGammaParallel from euclideanGamma_isHermitian 0]
  norm_num

theorem chord_rest_projector_ne_zero : chordRestProjector ≠ 0 := by
  intro h
  have h₀ := congrArg (fun A : DiracMatrix => A 0 0) h
  norm_num [chordRestProjector, chordGammaParallel, euclideanGamma] at h₀

/-- The same continued free Dirac numerator as in the unperturbed action,
with axial variable measured along the positive carrier unit. -/
def chordFreeAxialNumerator (m : ℝ) (z : ℂ) : DiracMatrix :=
  (-(Complex.I * z)) • chordGammaParallel + (m : ℂ) • 1

theorem chord_rest_normalized_residue (m : ℝ) (hm : 0 < m) :
    (2 * (m : ℂ))⁻¹ • chordFreeAxialNumerator m (chordRest m).1 =
      chordRestProjector := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [chordFreeAxialNumerator, show -(Complex.I * (chordRest m).1) = (m : ℂ) by
    simp only [chordRest, ← mul_assoc, Complex.I_mul_I]; ring]
  rw [← smul_add, smul_smul, add_comm, chordRestProjector]
  congr 1
  field_simp

/-- The slope used in the normalized free residue is the slope of the
Lorentzian denominator on the same unit carrier, at real energy m. -/
theorem chord_rest_shell_hasDerivAt (m : ℝ) :
    HasDerivAt (fun p => shellSquare p 0 - m ^ 2) (2 * m) m := by
  simpa [shellSquare] using ((hasDerivAt_id m).pow 2).sub_const (m ^ 2)

/-- Spin contraction of the analytic carrier derivative of the Gaussian
Wilson symbol. The two free rest residues are the same projector. -/
def chordAxialVertex (σ : ℝ) (k : ChordMomentum) : DiracMatrix :=
  (chordAxialDerivative σ k).1 • chordGammaParallel +
    ∑ j : Fin 3, (chordAxialDerivative σ k).2 j • euclideanGamma j.succ

theorem chord_axial_vertex_entire (σ : ℝ) (k : ChordMomentum) :
    AnalyticAt ℂ (chordAxialVertex σ) k := by
  have hg := chord_gaussian_entire σ k
  have h₀ := (ContinuousLinearMap.fst ℂ ℂ (Fin 3 → ℂ)).analyticAt k
  unfold chordAxialVertex chordAxialDerivative
  dsimp
  apply AnalyticAt.add
  · have hA : AnalyticAt ℂ (fun q : ChordMomentum => 1 - 2 * (σ : ℂ)^2 * q.1^2) k :=
      analyticAt_const.sub (analyticAt_const.mul (h₀.pow 2))
    exact (hg.mul hA).smul analyticAt_const
  · apply Finset.analyticAt_fun_sum
    intro j _
    have hⱼ := ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin 3 → ℂ))).analyticAt k
    have hB : AnalyticAt ℂ (fun q : ChordMomentum => -2 * (σ : ℂ)^2 * q.1 * q.2 j) k :=
      (analyticAt_const.mul h₀).mul hⱼ
    exact (hg.mul hB).smul analyticAt_const

theorem chord_axial_vertex_at_rest (m σ : ℝ) :
    chordRestProjector * chordAxialVertex σ (chordRest m) * chordRestProjector =
      (chordChargeFactor (m ^ 2 * σ ^ 2) : ℂ) • chordRestProjector := by
  simp only [chordAxialVertex, chord_axial_derivative_at_rest, Pi.zero_apply, zero_smul,
    Finset.sum_const_zero, add_zero, Matrix.mul_smul, Matrix.smul_mul, chord_rest_projector_gamma]

/-- With the common Dirac vertex phase removed, the coefficient relative
to the nonzero unit-charge rest matrix is the oriented coupling times g. -/
theorem chord_rest_charge_ratio (m σ e : ℝ) (q : ℂ) :
    chordRestProjector * ((e : ℂ) • chordAxialVertex σ (chordRest m)) *
        chordRestProjector = q • chordRestProjector ↔
      q = ((e * chordChargeFactor (m ^ 2 * σ ^ 2) : ℝ) : ℂ) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, chord_axial_vertex_at_rest, smul_smul,
    ← Complex.ofReal_mul]
  exact ⟨fun h => (smul_left_injective ℂ chord_rest_projector_ne_zero h).symm,
    fun h => by rw [h]⟩

end UV.SectorPlane
