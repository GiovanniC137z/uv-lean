import UV.ContinueNormalLegTransfer
import UV.ContinueNormalCoverConvolution
import UV.ContinueNormalLatticeGraph

/-! Ordered open lines in the three-compression model. A first-order
vertex contributes two independent shell compressions on adjacent charged
momenta. The external free propagators are included in the word. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter UV.SectorPlane
open scoped Matrix.Norms.L2Operator

namespace UV
variable {ι : Type*} [Fintype ι]

def compressedOpenFactor (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (u : UnitVector OSFourSpace) (p q : OSFourSpace) : DiracMatrix :=
  (Complex.I*(normalLegForm L T ξ p:ℂ)*(normalLegForm L T ξ q:ℂ)) • (normalDiracFrequency m p ξ * diracSlash u.val)

def compressedOpenWord {r : ℕ} (m L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (u : Fin r → UnitVector OSFourSpace) (p : Fin (r+1) → OSFourSpace) : DiracMatrix :=
  normalOrderedWord (fun j => compressedOpenFactor m L T ξ (u j) (p j.castSucc) (p j.succ)) * normalDiracFrequency m (p (Fin.last r)) ξ

theorem compressed_open_factor_bound {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (u : UnitVector OSFourSpace) (p q : OSFourSpace) :
    ‖compressedOpenFactor m L T ξ u p q‖ ≤ |normalLegForm L T ξ p| * m⁻¹ := by
  have hq : |normalLegForm L T ξ q| ≤ 1 := (Complex.abs_re_le_norm _).trans (normal_shell_characteristic_le_one _)
  simp only [compressedOpenFactor,norm_smul,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  have h := norm_mul_le (normalDiracFrequency m p ξ) (diracSlash u.val)
  rw [wilson_slash_opnorm,u.property,mul_one] at h
  exact mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) hq) (h.trans (normal_frequency_mass_bound hm p ξ)) (norm_nonneg _) (abs_nonneg _)

theorem compressed_open_marked_bound {r : ℕ} {m : ℝ} (hm : 0 < m) (L : ℝ) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι)
    (ξ : ℝ) (u : Fin (r+1) → UnitVector OSFourSpace) (p : Fin (r+1+1) → OSFourSpace) :
    ‖compressedOpenWord m L T ξ u p‖ ≤ |normalLegForm L T ξ (p 0)| * m⁻¹^(r+2) := by
  let A := fun j : Fin (r+1) => compressedOpenFactor m L T ξ (u j) (p j.castSucc) (p j.succ)
  have ha j : ‖A j‖ ≤ m⁻¹ := by
    exact (compressed_open_factor_bound hm L T ξ _ _ _).trans (mul_le_of_le_one_left (inv_nonneg.mpr hm.le)
      ((Complex.abs_re_le_norm _).trans (normal_shell_characteristic_le_one _)))
  have ht : ‖normalOrderedWord (fun j : Fin r => A j.succ)‖ ≤ m⁻¹^r := by
    apply (List.norm_prod_le _).trans
    rw [List.map_ofFn,List.prod_ofFn]
    simpa using Finset.prod_le_prod (s := (Finset.univ : Finset (Fin r))) (fun j _ => norm_nonneg (A j.succ)) (fun j _ => ha j.succ)
  change ‖(List.ofFn A).prod*_‖ ≤ _
  rw [List.ofFn_succ,List.prod_cons]
  apply (norm_mul_le _ _).trans
  apply (mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (compressed_open_factor_bound hm L T ξ _ _ _) ht (norm_nonneg _) (by positivity)))
    (normal_frequency_mass_bound hm _ _) (norm_nonneg _) (by positivity)).trans_eq
  simp only [Fin.castSucc_zero,pow_succ]; ring

theorem compressed_endpoint_form_bound {L : ℝ} (hL : 0 < L) (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ p, |normalLegForm L T ξ p| ≤ B*normalPhotonWeight 2 ξ := by
  have hd := T.toLinearMap.finrank_le_finrank_of_injective T.injective
  rw [finrank_euclideanSpace_fin,finrank_euclideanSpace] at hd
  obtain ⟨C,hC,h⟩ := normal_shell_characteristic_decay ι (by omega)
  let D := 1+L⁻¹
  refine ⟨C*D^2,by positivity,fun ξ p => ?_⟩
  let P := normalBallJoin ξ p
  have hn : |ξ| ≤ ‖P‖ := by
    dsimp [P]; nlinarith [normal_ball_join_norm ξ p,sq_abs ξ,norm_nonneg (normalBallJoin ξ p),abs_nonneg ξ,sq_nonneg ‖p‖]
  have hrel : 1+|ξ| ≤ D*(1+L*‖P‖) := by
    have he : L⁻¹*(L*‖P‖)=‖P‖ := by rw [←mul_assoc,inv_mul_cancel₀ hL.ne',one_mul]
    dsimp [D]; nlinarith [inv_nonneg.mpr hL.le,mul_nonneg hL.le (norm_nonneg P)]
  have hc := (Complex.abs_re_le_norm _).trans (h (L • T P))
  rw [norm_smul,T.norm_map,Real.norm_of_nonneg hL.le] at hc
  apply hc.trans
  rw [normalPhotonWeight,Real.norm_eq_abs,←div_eq_mul_inv,div_le_div_iff₀ (by positivity) (by positivity)]
  simpa only [mul_pow,mul_assoc] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrel 2) hC.le

local instance : MeasurableSpace DiracMatrix := borel _
local instance : BorelSpace DiracMatrix := ⟨rfl⟩

theorem compressed_open_measurable {Z : Type*} [MeasurableSpace Z] {r : ℕ} {m : ℝ} (hm : 0 < m) (L : ℝ)
    (T : NormalBall 5 →ₗᵢ[ℝ] WilsonBallSpace ι) (ξ : ℝ) (u : Fin r → UnitVector OSFourSpace)
    {p : Z → Fin (r+1) → OSFourSpace} (hp : ∀ j, Measurable (p · j)) :
    Measurable (fun z => compressedOpenWord m L T ξ u (p z)) := by
  have hf (j) := (Complex.continuous_ofReal.comp (normal_leg_form_continuous L T ξ)).measurable.comp (hp j)
  have hs (j) := (normal_frequency_continuous hm ξ).measurable.comp (hp j)
  apply Measurable.mul _ (hs _)
  apply normal_ordered_measurable
  intro j
  exact ((measurable_const.mul (hf j.castSucc)).mul (hf j.succ)).smul ((hs j.castSucc).mul_const _)

end UV
