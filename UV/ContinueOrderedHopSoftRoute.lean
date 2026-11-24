import UV.ContinueOrderedHopJointFourier
import UV.ContinueOrderedCurrentWard

/-! Basepoint differences on a complete path. Each interpolation phase is
a product of translations of individual heat and carrier factors. The
linear prefactor is an actual sum of individual duration derivatives and
zero-momentum straight-link marks in a unit spatial direction. -/

noncomputable section

open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace UV.SectorPlane

/-- At vanishing spatial momentum any unit axis represents the zero vector. -/
def orderedHopSoftDirection (p : Spatial) : UnitVector Spatial :=
  if h : p = 0 then ⟨EuclideanSpace.single 0 1, by simp⟩
  else ⟨‖p‖⁻¹ • p, by rw [norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]⟩

theorem orderedHop_soft_direction (p : Spatial) : ‖p‖ • (orderedHopSoftDirection p).val = p := by
  by_cases h : p = 0
  · simp [h]
  · simp [orderedHopSoftDirection,h,smul_smul]

private theorem relative_phase (b y : ℝ) :
    openingFourierWave 1 (b+y) - openingFourierWave 1 b =
      (Complex.I*(y:ℂ))*openingFourierWave 1 b * (∫ θ in (0:ℝ)..1, openingFourierWave y θ) := by
  let c := (y:ℂ)*Complex.I
  have hd (θ : ℝ) : HasDerivAt (fun t : ℝ => Complex.exp ((t:ℂ)*c))
      (c*Complex.exp ((θ:ℂ)*c)) θ := by
    simpa [mul_comm] using (((hasDerivAt_id (θ:ℂ)).mul_const c).cexp).comp_ofReal
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0:ℝ)) (b := 1) (fun t _ => hd t)
    ((show Continuous (fun t : ℝ => c*Complex.exp ((t:ℂ)*c)) by fun_prop).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at he
  simp only [Complex.ofReal_one,one_mul,Complex.ofReal_zero,zero_mul,Complex.exp_zero] at he
  have ht : (fun θ : ℝ => openingFourierWave y θ) = fun θ : ℝ => Complex.exp ((θ:ℂ)*c) := by
    funext θ; unfold openingFourierWave c; congr 1; ring
  rw [ht,mul_right_comm,show Complex.I*(y:ℂ) = c by unfold c; ring,he]
  simp only [openingFourierWave,Complex.ofReal_one,one_mul,Complex.ofReal_add,add_mul,Complex.exp_add,c]
  ring

/-- A weighted finite sum of interval and displacement contributions describes
both a vertical marking position and any interpolation point on a horizontal
hop. The formula simultaneously retains the original momenta and extracts
the scalar or transverse external soft factor. -/
theorem orderedHop_soft_routed_phase {ι : Type*} [Fintype ι] (b R η μ ν : ℝ) (p : Spatial)
    (v : UnitVector Spatial) (hν : ν = R*η) (hp : p = (R*μ) • v.val)
    (A B d : ι → ℝ) (z : ι → Spatial) :
    openingFourierWave 1 (b+∑ i, (A i*ν*d i+B i*⟪z i,p⟫)) - openingFourierWave 1 b =
      (R:ℂ)*(∑ i, (((η*A i:ℝ):ℂ)*(Complex.I*(d i:ℂ)) +
        ((μ*B i:ℝ):ℂ)*twoBandLineMode v 0 (z i))) * openingFourierWave 1 b *
      (∫ θ in (0:ℝ)..1, ∏ i, openingFourierWave (θ*A i*ν) (d i) *
        twoBandDisplacementWave ((θ*B i) • p) (z i)) := by
  rw [relative_phase]
  congr 2
  · push_cast
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hν,hp,orderedHop_zero_spatial_mark,real_inner_smul_right]
    push_cast
    ring
  · funext θ
    simp only [openingFourierWave,twoBandDisplacementWave,real_inner_smul_right,
      ←Complex.exp_add,←Complex.exp_sum,Complex.ofReal_sum,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring

/-- The angular coefficients of every extracted four-momentum have modulus at
most one, including at the zero mode. -/
theorem orderedHop_transverse_soft_coordinates (ν : ℝ) (p : Spatial) :
    let Q := Real.sqrt (ν^2+‖p‖^2)
    ν = Q*(ν/Q) ∧ p = (Q*(‖p‖/Q)) • (orderedHopSoftDirection p).val ∧
      |ν/Q| ≤ 1 ∧ |‖p‖/Q| ≤ 1 := by
  intro Q
  have hs : Q^2 = ν^2+‖p‖^2 := Real.sq_sqrt (by positivity)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hν : |ν| ≤ Q := by nlinarith [sq_nonneg ‖p‖,sq_abs ν,abs_nonneg ν]
  have hp : ‖p‖ ≤ Q := by nlinarith [sq_nonneg ν,norm_nonneg p]
  by_cases h : Q = 0
  · have hz : ν = 0 := abs_eq_zero.mp (le_antisymm (h ▸ hν) (abs_nonneg ν))
    have hpz : p = 0 := norm_eq_zero.mp (le_antisymm (h ▸ hp) (norm_nonneg p))
    simp [h,hz,hpz]
  · have hpos := lt_of_le_of_ne hQ (Ne.symm h)
    have hq (x : ℝ) : Q*(x/Q) = x := by field_simp
    rw [hq,hq,orderedHop_soft_direction]
    simp only [true_and,abs_div,abs_of_pos hpos,abs_of_nonneg (norm_nonneg p)]
    constructor
    · exact (div_le_one hpos).mpr hν
    · exact (div_le_one hpos).mpr hp

end UV.SectorPlane
