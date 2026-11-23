import UV.ContinueWilsonChargedPole
import UV.ContinueRelativeCharge

/-! Reconstruction of the four-component rest resolvent from its two
time-spin projections in the repository's Euclidean Clifford representation. -/

noncomputable section

open Matrix Filter UV.SectorPlane
open scoped Topology Matrix

namespace UV

def wilsonSpinMatrix (p q : ℂ) : DiracMatrix :=
  p • chordRestProjector + q • (1 - chordRestProjector)

theorem wilsonSpinMatrix_same (p : ℂ) : wilsonSpinMatrix p p = p • 1 := by
  unfold wilsonSpinMatrix
  module

theorem wilsonSpinMatrix_clifford (g k : ℂ) :
    wilsonSpinMatrix (g+k) (g-k) = g • 1 + k • chordGammaParallel := by
  unfold wilsonSpinMatrix chordRestProjector
  module

theorem wilsonSpinMatrix_mul (p q r s : ℂ) :
    wilsonSpinMatrix p q * wilsonSpinMatrix r s = wilsonSpinMatrix (p*r) (q*s) := by
  let P := chordRestProjector
  have he : P*P=P := chord_rest_projector_idempotent
  have h₁ : P*(1-P) = 0 := by rw [mul_sub,mul_one,he,sub_self]
  have h₂ : (1-P)*P = 0 := by rw [sub_mul,one_mul,he,sub_self]
  have h₃ : (1-P)*(1-P) = 1-P := by rw [sub_mul,one_mul,h₁,sub_zero]
  change (p • P + q • (1-P)) * (r • P + s • (1-P)) = _
  simp only [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,h₁,h₂,h₃,he,smul_zero,add_zero,zero_add,smul_smul]
  rw [mul_comm r p,mul_comm s q]
  rfl

theorem wilsonSpinMatrix_inverse {p q : ℂ} (hp : p ≠ 0) (hq : q ≠ 0) :
    (wilsonSpinMatrix p q)⁻¹ = wilsonSpinMatrix p⁻¹ q⁻¹ := by
  apply Matrix.inv_eq_right_inv
  simp only [wilsonSpinMatrix_mul,mul_inv_cancel₀ hp,mul_inv_cancel₀ hq,wilsonSpinMatrix_same,one_smul]

/-- Both complementary spin subspaces occur in this representation. -/
theorem wilson_spin_subspaces_nonzero : chordRestProjector ≠ 0 ∧ (1:DiracMatrix)-chordRestProjector ≠ 0 := by
  refine ⟨chord_rest_projector_ne_zero,fun h => ?_⟩
  have he := congrArg (fun A : DiracMatrix => A 0 0) h
  norm_num [chordRestProjector,chordGammaParallel,euclideanGamma] at he

def WilsonRestLaw.restDiracMatrix {L : ℝ} (D : WilsonRestLaw L) (lam : ℝ) (z : ℂ) : DiracMatrix :=
  (L:ℂ)⁻¹ • (1 - (lam:ℂ) • (D.complexMoment 0 z • 1 +
    ((1/(2*(L:ℂ))) * D.complexMoment 1 z) • chordGammaParallel))

theorem WilsonRestLaw.rest_dirac_matrix_blocks {L : ℝ} (D : WilsonRestLaw L) (lam : ℝ) (z : ℂ) :
    D.restDiracMatrix lam z =
      wilsonSpinMatrix (D.restDenominator lam 1 z/(L:ℂ)) (D.restDenominator lam (-1) z/(L:ℂ)) := by
  have hh := wilsonSpinMatrix_clifford (D.complexMoment 0 z) (1/(2*(L:ℂ))*D.complexMoment 1 z)
  unfold WilsonRestLaw.restDiracMatrix
  rw [← hh]
  unfold wilsonSpinMatrix WilsonRestLaw.restDenominator WilsonRestLaw.complexBlock
  push_cast
  simp only [neg_mul,sub_eq_add_neg,div_eq_mul_inv]
  module

/-- Away from the poles, inverting the actual matrix and multiplying by
`γ_parallel` gives the stated signed scalar endpoints on the two blocks. -/
theorem WilsonRestLaw.rest_dirac_inverse_gamma {L : ℝ} (D : WilsonRestLaw L) (lam : ℝ) (z : ℂ)
    (hp : D.restDenominator lam 1 z ≠ 0) (hq : D.restDenominator lam (-1) z ≠ 0) :
    (D.restDiracMatrix lam z)⁻¹ * chordGammaParallel = wilsonSpinMatrix (D.restEndpoint lam 1 z) (D.restEndpoint lam (-1) z) := by
  have hL := Complex.ofReal_ne_zero.mpr D.length_pos.ne'
  have hγ : wilsonSpinMatrix 1 (-1) = chordGammaParallel := by simpa using wilsonSpinMatrix_clifford 0 1
  rw [D.rest_dirac_matrix_blocks,wilsonSpinMatrix_inverse (div_ne_zero hp hL) (div_ne_zero hq hL),
    ← hγ,wilsonSpinMatrix_mul]
  congr 1 <;> simp [WilsonRestLaw.restEndpoint,div_eq_mul_inv,mul_comm]

theorem WilsonRestLaw.rest_weight_regular_contact {L lam σ M : ℝ} (D : WilsonRestLaw L)
    (hlam : 0 < lam) (hM : D.block σ 0 M = lam⁻¹) (hd : 0 < D.block σ 1 M)
    {C : ℂ → ℂ} (hC : ContinuousAt C (M:ℂ)) :
    Tendsto (fun z : ℂ => ((M:ℂ)-z)*(D.restEndpoint lam σ z + C z)) (𝓝[≠] (M:ℂ))
      (𝓝 ((σ*L/(lam*D.block σ 1 M) : ℝ):ℂ)) := by
  have hId : Tendsto (fun z : ℂ => (M:ℂ)-z) (𝓝[≠] (M:ℂ)) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (M:ℂ))).sub (show Tendsto id (𝓝[≠] (M:ℂ)) (𝓝 (M:ℂ)) from nhdsWithin_le_nhds)
  simpa only [mul_add,zero_mul,add_zero] using (D.rest_weight_limit hlam hM hd).add
    (hId.mul (hC.tendsto.mono_left nhdsWithin_le_nhds))

end UV
