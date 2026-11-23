import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Matrix
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-! The angular Hilbert–Schmidt bound for the quartic normal collar.
The Fourier states use normalized circle Haar measure. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Matrix.Norms.Frobenius
namespace UV.RoughCurvature

def angularWeight (j : ℤ) : ℝ := if j = 0 then 1 else (2 * |(j : ℝ)|)⁻¹

theorem angularWeight_nonneg (j : ℤ) : 0 ≤ angularWeight j := by
  unfold angularWeight
  split <;> positivity

private theorem angularWeight_square (j : ℤ) :
    angularWeight j ^ 2 = (if j = 0 then 1 else 0) + (1 / 4) * (1 / (j : ℝ)^2) := by
  by_cases h : j = 0
  · simp [h, angularWeight]
  · simp only [angularWeight, h, if_false, zero_add, inv_pow, mul_pow, sq_abs]
    norm_num [mul_comm]

theorem angularWeight_square_sum :
    HasSum (fun j : ℤ => angularWeight j ^ 2) (1 + Real.pi ^ 2 / 12) := by
  classical
  have hs : Summable (fun j : ℤ => 1 / (j : ℝ)^2) :=
    Real.summable_one_div_int_pow.2 (by norm_num)
  have hnat : (∑' j : ℕ+, 1 / ((j : ℕ) : ℝ)^2) = Real.pi ^ 2 / 6 := by
    have h := (tsum_zero_pnat_eq_tsum_nat hasSum_zeta_two.summable).trans hasSum_zeta_two.tsum_eq
    simpa using h
  have hz : (∑' j : ℤ, 1 / (j : ℝ)^2) = 2 * (Real.pi ^ 2 / 6) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (fun j => by simp) hs]
    simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      div_zero, zero_add, Int.cast_natCast, hnat, two_nsmul]
    ring
  have h₀ : HasSum (fun j : ℤ => if j = 0 then (1:ℝ) else 0) 1 :=
    hasSum_ite_eq 0 1
  convert h₀.add (hs.hasSum.mul_left (1 / 4)) using 1
  · funext j
    exact angularWeight_square j
  · rw [hz]
    ring

private theorem angularWeight_finite_square (s : Finset ℤ) :
    ∑ k ∈ s, angularWeight k ^ 2 ≤ 1 + Real.pi ^ 2 / 12 :=
  angularWeight_square_sum.tsum_eq ▸ Summable.sum_le_tsum s (fun _ _ => sq_nonneg _) angularWeight_square_sum.summable

private theorem angularWeight_shift_bound (s : Finset ℤ) (d : ℤ) :
    ∑ k ∈ s, angularWeight (k+d) * angularWeight k ≤ 1 + Real.pi ^ 2 / 12 := by
  let C := 1 + Real.pi ^ 2 / 12
  have hs := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => angularWeight (k+d)) angularWeight
  have h₁ : ∑ k ∈ s, angularWeight (k+d)^2 ≤ C := by
    have H := angularWeight_finite_square (s.image (fun k : ℤ => k+d))
    rw [Finset.sum_image (fun a _ b _ hab => add_right_cancel hab)] at H
    exact H
  have h₂ := angularWeight_finite_square s
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun k _ => mul_nonneg (angularWeight_nonneg _) (angularWeight_nonneg _))) hC).1
  exact hs.trans (by
    rw [pow_two]
    exact mul_le_mul h₁ h₂ (Finset.sum_nonneg (fun k _ => sq_nonneg _)) hC)

def angularMatrix (s : Finset ℤ) (a : ℤ → ℂ) : Matrix s s ℝ :=
  fun j k => Real.sqrt (angularWeight j * angularWeight k) * ‖a ((j : ℤ)-k)‖

private theorem angularMatrix_square (s : Finset ℤ) (a : ℤ → ℂ) (j k : s) :
    ‖angularMatrix s a j k‖ ^ 2 = angularWeight j * angularWeight k * ‖a ((j : ℤ)-k)‖ ^ 2 := by
  simp [angularMatrix, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt,
    mul_nonneg (angularWeight_nonneg _) (angularWeight_nonneg _)]

/-- Every finite compression of the Fourier insertion pays the same
Hilbert–Schmidt constant, with no dimension-dependent loss. -/
theorem angularMatrix_bound (s : Finset ℤ) (a : ℤ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ S : Finset ℤ, ∑ d ∈ S, ‖a d‖ ^ 2 ≤ M ^ 2) :
    ‖angularMatrix s a‖ ≤ Real.sqrt (1 + Real.pi ^ 2 / 12) * M := by
  classical
  let C := 1 + Real.pi ^ 2 / 12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let D := (s ×ˢ s).image (fun p : ℤ × ℤ => p.1 - p.2)
  let f := fun (p : ℤ × ℤ) => angularWeight (p.2+p.1) * angularWeight p.2 * ‖a p.1‖^2
  have hnonneg (p : ℤ × ℤ) : 0 ≤ f p :=
    mul_nonneg (mul_nonneg (angularWeight_nonneg _) (angularWeight_nonneg _)) (sq_nonneg _)
  have hmap : (s ×ˢ s).image (fun p : ℤ × ℤ => (p.1-p.2,p.2)) ⊆ D ×ˢ s := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩,(Finset.mem_product.mp hq).2⟩
  have hsum : ∑ j ∈ s, ∑ k ∈ s, angularWeight j * angularWeight k * ‖a (j-k)‖^2 ≤ C * M^2 := by
    calc
      _ = ∑ p ∈ (s ×ˢ s).image (fun p : ℤ × ℤ => (p.1-p.2,p.2)), f p := by
        rw [Finset.sum_image, Finset.sum_product]
        · apply Finset.sum_congr rfl; intro j hj
          apply Finset.sum_congr rfl; intro k hk
          simp [f, add_comm k]
        · intro p hp q hq hpq
          have h₂ := congrArg (Prod.snd : ℤ × ℤ → ℤ) hpq
          have h₁ := congrArg (Prod.fst : ℤ × ℤ → ℤ) hpq
          change p.2 = q.2 at h₂
          change p.1-p.2 = q.1-q.2 at h₁
          exact Prod.ext (by omega) h₂
      _ ≤ ∑ p ∈ D ×ˢ s, f p := Finset.sum_le_sum_of_subset_of_nonneg hmap (fun p _ _ => hnonneg p)
      _ ≤ C * M^2 := by
        rw [Finset.sum_product]
        calc
          _ ≤ ∑ d ∈ D, C * ‖a d‖^2 := by
            apply Finset.sum_le_sum
            intro d hd
            change (∑ y ∈ s, angularWeight (y+d) * angularWeight y * ‖a d‖^2) ≤ C * ‖a d‖^2
            rw [← Finset.sum_mul]
            exact mul_le_mul_of_nonneg_right (angularWeight_shift_bound s d) (sq_nonneg _)
          _ ≤ C * M^2 := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (hA D) hC
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hM)).1
  rw [mul_pow, Real.sq_sqrt hC, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two, angularMatrix_square]
  have hsub (f : ℤ → ℝ) : ∑ a : s, f a = ∑ a ∈ s, f a :=
    (Finset.sum_subtype s (fun _ => Iff.rfl) f).symm
  calc
    (∑ j : s, ∑ k : s, angularWeight j * angularWeight k * ‖a ((j : ℤ)-k)‖^2) =
        ∑ j : s, ∑ k ∈ s, angularWeight j * angularWeight k * ‖a ((j : ℤ)-k)‖^2 :=
      Finset.sum_congr rfl (fun j _ => hsub (fun k => angularWeight j * angularWeight k * ‖a ((j : ℤ)-k)‖^2))
    _ = ∑ j ∈ s, ∑ k ∈ s, angularWeight j * angularWeight k * ‖a (j-k)‖^2 :=
      hsub (fun j => ∑ k ∈ s, angularWeight j * angularWeight k * ‖a (j-k)‖^2)
    _ ≤ _ := hsum

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev AngularProfile := Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))

theorem angularMatrix_parseval (s : Finset ℤ) (g : AngularProfile) :
    ‖angularMatrix s (fourierCoeff g)‖ ≤ Real.sqrt (1 + Real.pi ^ 2 / 12) * ‖g‖ := by
  apply angularMatrix_bound s _ (norm_nonneg _)
  intro S
  simp_rw [← fourierBasis_repr]
  have hsum := lp.hasSum_norm (show 0 < (2 : ℝ≥0∞).toReal by norm_num) (fourierBasis.repr g)
  have h := Summable.sum_le_tsum S (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) hsum.summable
  rw [hsum.tsum_eq] at h
  simpa [Real.rpow_ofNat] using h

end UV.RoughCurvature
