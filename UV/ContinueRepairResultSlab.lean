import UV.ContinueRepairResultKinetic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The massive one-sided carrier kernel and the actual Gaussian spatial
pair hop have square-summable mixed kernel on a finite slab times a
rectangular spatial torus. The spatial mode sum runs over all integer
triples. The nonnegative time lag accounts for either one-sided slot. -/

noncomputable section
open Set MeasureTheory Matrix
open UV.FurtherOptical
open scoped Matrix

namespace UV

/-- Intrinsic reciprocal momenta of a rectangular torus. The positive
coordinate spacings may be chosen as 2π divided by the three periods. -/
def repairTorusMomentum (δ₁ δ₂ δ₃ : ℝ) (n : ℤ × ℤ × ℤ) : ChargeSpatialMomentum :=
  WithLp.toLp 2 ![δ₁*(n.1:ℝ), δ₂*(n.2.1:ℝ), δ₃*(n.2.2:ℝ)]

private theorem repair_torus_norm_sq (δ₁ δ₂ δ₃ : ℝ) (n : ℤ × ℤ × ℤ) :
    ‖repairTorusMomentum δ₁ δ₂ δ₃ n‖^2 = (δ₁*(n.1:ℝ))^2+(δ₂*(n.2.1:ℝ))^2+(δ₃*(n.2.2:ℝ))^2 := by
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_three]
  simp [repairTorusMomentum,mul_pow]

private theorem reciprocal_tick_gaussian {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    Summable (fun n : ℤ => Real.exp (-τ*(δ*(n:ℝ))^2)) := by
  have hn : Summable (fun n : ℕ => Real.exp (-τ*(δ*(n:ℝ))^2)) := by
    have hs := Real.summable_pow_mul_exp_neg_nat_mul 0 (mul_pos hτ (sq_pos_of_pos hδ))
    simp only [pow_zero,one_mul] at hs
    apply hs.of_nonneg_of_le (fun _ => Real.exp_nonneg _)
    intro n
    apply Real.exp_le_exp.mpr
    have hh : (n:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast (Nat.le_self_pow (by norm_num : 2 ≠ 0) n)
    nlinarith [mul_le_mul_of_nonneg_left hh (mul_pos hτ (sq_pos_of_pos hδ)).le]
  apply summable_int_iff_summable_nat_and_neg.mpr
  exact ⟨by simpa using hn,by simpa [mul_neg] using hn⟩

theorem repair_gaussian_torus_summable {τ δ₁ δ₂ δ₃ : ℝ} (hτ : 0 < τ)
    (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (h₃ : 0 < δ₃) :
    Summable (fun n : ℤ × ℤ × ℤ => attenuation τ (repairTorusMomentum δ₁ δ₂ δ₃ n)) := by
  have h := (reciprocal_tick_gaussian hτ h₁).mul_of_nonneg
    ((reciprocal_tick_gaussian hτ h₂).mul_of_nonneg (reciprocal_tick_gaussian hτ h₃)
      (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _))
    (fun _ => Real.exp_nonneg _) (fun _ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  apply h.congr
  intro n
  rw [attenuation,repair_torus_norm_sq]
  simp only [←Real.exp_add]
  congr 1
  ring

/-- The unmarked hopping part of the Hamiltonian, with the diagonal
slot removed. -/
def repairPairHop (m τ g : ℝ) (k : ChargeSpatialMomentum) : DiracMatrix :=
  repairHamiltonian m τ g k-repairHamiltonian m τ 0 k

theorem repair_pair_hop_hs_sq (m τ g : ℝ) (k : ChargeSpatialMomentum) (a : ℝ) :
    chargeInclusiveSquare ((a:ℂ) • repairPairHop m τ g k) = 4*a^2*(g*attenuation τ k)^2*‖k‖^2 := by
  let w := repairCliffordCoefficients m τ g k - repairCliffordCoefficients m τ 0 k
  have he : repairPairHop m τ g k = diracSlash w := (slash_sub _ _).symm
  have hn : ‖w‖^2 = (g*attenuation τ k)^2*‖k‖^2 := by
    rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,EuclideanSpace.norm_sq_eq,Finset.mul_sum]
    change ‖diagonal m τ k-diagonal m τ k‖^2 +
      (∑ j : Fin 3, ‖(g*attenuation τ k)*k j-(0*attenuation τ k)*k j‖^2) = _
    simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add,zero_mul,sub_zero,Real.norm_eq_abs,sq_abs]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,chargeInclusiveSquare_eq_trace,conjTranspose_smul,slash_adjoint,smul_mul_smul,diracSlash_sq,smul_smul,
    Matrix.trace_smul,Matrix.trace_one]
  norm_num [smul_eq_mul,Complex.mul_re]
  norm_cast
  rw [hn]
  ring

private theorem repair_pair_time_weight (m τ g : ℝ) (k : ChargeSpatialMomentum) (u : ℝ) :
    chargeInclusiveSquare ((Real.exp (-diagonal m τ k*u):ℂ) • repairPairHop m τ g k) =
      (4*(g*attenuation τ k)^2*‖k‖^2)*Real.exp ((-(2*diagonal m τ k))*u) := by
  rw [repair_pair_hop_hs_sq,←Real.exp_nat_mul]
  push_cast
  rw [show 2*(-diagonal m τ k*u) = -(2*diagonal m τ k)*u by ring]
  ring

/-- Exact time and slot integral of the free pair-hop envelope for a
mode k. The finite slab source time has length T. -/
theorem repair_pair_slab_mode_integral {m τ T : ℝ} (hm : 0 < m) (hτ : 0 ≤ τ) (hT : 0 ≤ T)
    (g : ℝ) (k : ChargeSpatialMomentum) :
    (∫ _ in Icc 0 T, ∫ u in Ioi (0:ℝ),
      chargeInclusiveSquare ((Real.exp (-diagonal m τ k*u):ℂ) • repairPairHop m τ g k)) =
      (2*T*g^2*‖k‖^2*attenuation τ k^2)/diagonal m τ k := by
  have hc := hm.trans_le (repair_diagonal_lower hm hτ k)
  simp_rw [repair_pair_time_weight]
  rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : -(2*diagonal m τ k) < 0),setIntegral_const]
  simp [Real.volume_real_Icc_of_le hT,smul_eq_mul]
  field_simp
  ring

/-- The mixed squared Hilbert–Schmidt envelope of S₀K₀ is finite with
no spatial mode cutoff and arbitrary finite real hopping g. -/
theorem repair_pair_slab_hilbert_schmidt {m τ T δ₁ δ₂ δ₃ : ℝ} (hm : 0 < m) (hτ : 0 < τ) (hT : 0 ≤ T)
    (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (h₃ : 0 < δ₃) (g : ℝ) :
    Summable (fun n : ℤ × ℤ × ℤ => let k := repairTorusMomentum δ₁ δ₂ δ₃ n
      ∫ _ in Icc 0 T, ∫ u in Ioi (0:ℝ), chargeInclusiveSquare ((Real.exp (-diagonal m τ k*u):ℂ) • repairPairHop m τ g k)) := by
  simp only [repair_pair_slab_mode_integral hm hτ.le hT]
  have hsum := (repair_gaussian_torus_summable hτ h₁ h₂ h₃).mul_left (2*T*g^2/(m*τ))
  apply hsum.of_nonneg_of_le
  · intro n
    exact div_nonneg (by positivity) (hm.trans_le (repair_diagonal_lower hm hτ.le _)).le
  · intro n
    let k := repairTorusMomentum δ₁ δ₂ δ₃ n
    let A := attenuation τ k
    have hA : 0 < A := Real.exp_pos _
    have ha : τ*‖k‖^2*A ≤ 1 := by
      dsimp [A,attenuation]
      rw [neg_mul,Real.exp_neg,←div_eq_mul_inv,div_le_one (Real.exp_pos _)]
      linarith [Real.add_one_le_exp (τ*‖k‖^2)]
    change 2*T*g^2*‖k‖^2*A^2/diagonal m τ k ≤ (2*T*g^2/(m*τ))*A
    rw [div_le_iff₀ (hm.trans_le (repair_diagonal_lower hm hτ.le k)),div_mul_eq_mul_div,
      div_mul_eq_mul_div,le_div_iff₀ (mul_pos hm hτ)]
    have hb := mul_le_mul_of_nonneg_left ha (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) hT) (sq_nonneg g)) (mul_pos hm hA).le)
    have hc := mul_le_mul_of_nonneg_left (repair_diagonal_lower hm hτ.le k) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) hT) (sq_nonneg g)) hA.le)
    nlinarith

private theorem count_slab_integrability (T : ℝ) (f : (ℤ × ℤ × ℤ) → ℝ → ℝ)
    (hm : ∀ n, Measurable (f n)) (hz : ∀ n u, 0 ≤ f n u)
    (hi : ∀ n, IntegrableOn (f n) (Ioi 0))
    (hs : Summable (fun n => ∫ _ in Icc 0 T, ∫ u in Ioi 0, f n u)) :
    Integrable (fun x : (ℤ × ℤ × ℤ) × (ℝ × ℝ) => f x.1 x.2.2)
      (Measure.count.prod ((volume.restrict (Icc (0:ℝ) T)).prod (volume.restrict (Ioi (0:ℝ))))) := by
  let μ := volume.restrict (Icc (0:ℝ) T)
  let ν := volume.restrict (Ioi (0:ℝ))
  have ht (n) : Integrable (fun y : ℝ × ℝ => f n y.2) (μ.prod ν) := (hi n).comp_snd μ
  have hMeas : Measurable (fun x : (ℤ × ℤ × ℤ) × (ℝ × ℝ) => f x.1 x.2.2) :=
    measurable_from_prod_countable_right (fun n => (hm n).comp measurable_snd)
  apply (integrable_prod_iff hMeas.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall ht,integrable_count_iff.mpr (hs.congr ?_)⟩
  intro n
  change (∫ _ in Icc 0 T, ∫ u in Ioi (0:ℝ), f n u) = ‖∫ y, ‖f n y.2‖ ∂μ.prod ν‖
  simp_rw [Real.norm_of_nonneg (hz _ _)]
  have hpos : 0 ≤ ∫ y : ℝ × ℝ, f n y.2 ∂μ.prod ν := integral_nonneg fun y => hz n y.2
  rw [Real.norm_of_nonneg hpos,integral_prod _ (ht n)]

/-- The independent discrete carrier momentum, slab insertion time and
one-sided separation are jointly absolutely integrable against their
product measure. -/
theorem repair_pair_slab_joint_integrability {m τ T δ₁ δ₂ δ₃ : ℝ} (hm : 0 < m) (hτ : 0 < τ) (hT : 0 ≤ T)
    (h₁ : 0 < δ₁) (h₂ : 0 < δ₂) (h₃ : 0 < δ₃) (g : ℝ) :
    let k := repairTorusMomentum δ₁ δ₂ δ₃
    let f := fun n u => chargeInclusiveSquare ((Real.exp (-diagonal m τ (k n)*u):ℂ) • repairPairHop m τ g (k n))
    Integrable (fun x : (ℤ × ℤ × ℤ) × (ℝ × ℝ) => f x.1 x.2.2)
      (Measure.count.prod ((volume.restrict (Icc (0:ℝ) T)).prod (volume.restrict (Ioi (0:ℝ))))) := by
  let k := repairTorusMomentum δ₁ δ₂ δ₃
  let f := fun n u => chargeInclusiveSquare ((Real.exp (-diagonal m τ (k n)*u):ℂ) • repairPairHop m τ g (k n))
  apply count_slab_integrability T f _ _ _ (repair_pair_slab_hilbert_schmidt hm hτ hT h₁ h₂ h₃ g)
  · intro n
    simp only [f,repair_pair_time_weight]
    exact measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))
  · intro n u
    dsimp only [f]; rw [repair_pair_time_weight]; positivity
  · intro n
    simp only [f,repair_pair_time_weight]
    exact (integrableOn_exp_mul_Ioi (by linarith [repair_diagonal_lower hm hτ.le (k n)] : -(2*diagonal m τ (k n)) < 0) 0).const_mul _

end UV
