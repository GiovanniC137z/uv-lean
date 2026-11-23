import UV.ContinueWilsonShellEndpoint
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Matrix spectral weight at the higher positive-energy pole of the
actual charged endpoint. A unit spinor tests the failure of positivity. -/

noncomputable section

open Set Filter Matrix UV.SectorPlane
open scoped Topology Matrix ComplexOrder

namespace UV

theorem WilsonRestLaw.rest_regular_rescaled {L : ℝ} (D : WilsonRestLaw L)
    {lam σ M : ℝ} (h : D.restDenominator lam σ (M:ℂ) ≠ 0) :
    Tendsto (fun z : ℂ => ((M:ℂ)-z)*D.restEndpoint lam σ z) (𝓝[≠] (M:ℂ)) (𝓝 0) := by
  have hc : ContinuousAt (D.restEndpoint lam σ) (M:ℂ) :=
    continuousAt_const.div (D.rest_denominator_derivative lam σ _).continuousAt h
  have hId : Tendsto id (𝓝[≠] (M:ℂ)) (𝓝 (M:ℂ)) := nhdsWithin_le_nhds
  simpa only [sub_self,zero_mul] using ((tendsto_const_nhds (x := (M:ℂ))).sub hId).mul
    (hc.tendsto.mono_left nhdsWithin_le_nhds)

private theorem WilsonRestLaw.denominator_locally_nonzero {L : ℝ} (D : WilsonRestLaw L)
    {lam : ℝ} (hl : lam < 1) (σ : ℝ) (p : ℂ) :
    ∀ᶠ z in 𝓝[≠] p, D.restDenominator lam σ z ≠ 0 := by
  have hf : Differentiable ℂ (D.restDenominator lam σ) := fun z => (D.rest_denominator_derivative lam σ z).differentiableAt
  have hA := hf.differentiableOn.analyticOnNhd (s := univ) isOpen_univ
  exact (hA p (mem_univ p)).eventually_eq_zero_or_eventually_ne_zero.resolve_left (fun he =>
    D.rest_denominator_not_zero hl σ (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ p) he (mem_univ 0)))

/-- Componentwise spectral coefficient in the convention (M-z)D⁻¹γ. -/
theorem WilsonRestLaw.rest_dirac_weight_limit {L lam M P Q : ℝ} (D : WilsonRestLaw L) (hl : lam < 1)
    (hP : Tendsto (fun z : ℂ => ((M:ℂ)-z)*D.restEndpoint lam 1 z) (𝓝[≠] (M:ℂ)) (𝓝 (P:ℂ)))
    (hQ : Tendsto (fun z : ℂ => ((M:ℂ)-z)*D.restEndpoint lam (-1) z) (𝓝[≠] (M:ℂ)) (𝓝 (Q:ℂ)))
    (i j : Fin 4) :
    Tendsto (fun z : ℂ => ((M:ℂ)-z)*((D.restDiracMatrix lam z)⁻¹ * chordGammaParallel) i j)
      (𝓝[≠] (M:ℂ)) (𝓝 (wilsonSpinMatrix (P:ℂ) (Q:ℂ) i j)) := by
  have h := (hP.mul_const (chordRestProjector i j)).add (hQ.mul_const (((1:DiracMatrix)-chordRestProjector) i j))
  apply h.congr'
  filter_upwards [D.denominator_locally_nonzero hl 1 (M:ℂ),D.denominator_locally_nonzero hl (-1) (M:ℂ)] with z hp hq
  rw [D.rest_dirac_inverse_gamma lam z hp hq]
  simp only [wilsonSpinMatrix,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- A unit coordinate spinor has quadratic weight Z/2 on the upper pole. -/
theorem wilson_negative_weight_matrix {Z : ℝ} (hZ : Z < 0) :
    let v : EuclideanSpace ℂ (Fin 4) := EuclideanSpace.single 0 1
    ‖v‖ = 1 ∧ (star (fun k => v k) ⬝ᵥ (wilsonSpinMatrix 0 (Z:ℂ) *ᵥ fun k => v k)).re = Z/2 ∧
      ¬(wilsonSpinMatrix 0 (Z:ℂ)).PosSemidef := by
  have he : (star (Pi.single (0:Fin 4) (1:ℂ)) ⬝ᵥ (wilsonSpinMatrix 0 (Z:ℂ) *ᵥ Pi.single 0 1)).re = Z/2 := by
    rw [← Pi.single_star,star_one,Matrix.mulVec_single_one,single_one_dotProduct]
    change (wilsonSpinMatrix 0 (Z:ℂ) 0 0).re = Z/2
    norm_num [wilsonSpinMatrix,chordRestProjector,chordGammaParallel,euclideanGamma,Matrix.sub_apply,
      Matrix.add_apply,Matrix.smul_apply,Complex.mul_re]
    ring
  have hv : (fun k => (EuclideanSpace.single (0:Fin 4) (1:ℂ)) k) = Pi.single 0 1 := by
    funext k
    simp [EuclideanSpace.single_apply,Pi.single_apply]
  refine ⟨by simp,by simpa only [hv] using he,fun h => ?_⟩
  have hh := h.re_dotProduct_nonneg (Pi.single (0:Fin 4) (1:ℂ))
  change 0 ≤ (star (Pi.single (0:Fin 4) (1:ℂ)) ⬝ᵥ (wilsonSpinMatrix 0 (Z:ℂ) *ᵥ Pi.single 0 1)).re at hh
  rw [he] at hh
  linarith

set_option maxHeartbeats 1000000 in
/-- The matrix coefficient at the larger mass fails to be a positive
semidefinite atom for the same zero-background time-ordered endpoint. -/
theorem wilson_shell_negative_matrix_atom {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (T : OSFourSpace →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ M Z : ℝ, 0 < M ∧ Z < 0 ∧ ¬(wilsonSpinMatrix 0 (Z:ℂ)).PosSemidef ∧
      ∀ i j : Fin 4, Tendsto (fun z : ℂ => ((M:ℂ)-z) *
        ((((L:ℂ)⁻¹ • ((1:DiracMatrix)-(1/4:ℂ) • wilsonShellHop L T z))⁻¹ * chordGammaParallel) i j))
        (𝓝[≠] (M:ℂ)) (𝓝 (wilsonSpinMatrix 0 (Z:ℂ) i j)) := by
  let D := wilsonShellRestLaw hL (wilsonReadoutUnit T 0)
  obtain ⟨p,q,_,Z,hp,hpq,_,hZ,hpoles,_,_,hlim⟩ := (wilson_shell_charged_spectrum hL T).1
  have hz : D.restDenominator (1/4) 1 (q:ℂ) ≠ 0 := by
    intro he
    rcases (hpoles q).mp he with h | h <;> linarith
  refine ⟨q,Z,hp.trans hpq,hZ,(wilson_negative_weight_matrix hZ).2.2,fun i j => ?_⟩
  have h := D.rest_dirac_weight_limit (lam := 1/4) (P := 0) (by norm_num)
    (by simpa only [Complex.ofReal_zero] using D.rest_regular_rescaled hz) hlim i j
  convert h using 1
  · funext z
    rw [wilson_shell_hop_matrix hL]
    simp only [D,WilsonRestLaw.restDiracMatrix,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]

end UV
