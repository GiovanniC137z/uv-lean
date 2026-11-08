import UV.Kernel
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

noncomputable section
open Filter Set
open scoped Topology

namespace UV

/-- The geometric heat measure's explicit meromorphic continuation. -/
def gappedGeometricContinuation (z : ℂ) : ℂ := (2 * Complex.exp z - 1)⁻¹

def gappedGeometricPole (n : ℤ) : ℂ :=
  -(Real.log 2 : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

theorem gappedGeometricDenominator_analytic (z : ℂ) :
    AnalyticAt ℂ (fun w => 2 * Complex.exp w - 1) z := by fun_prop

theorem gappedGeometricContinuation_meromorphic :
    MeromorphicOn gappedGeometricContinuation univ := by
  intro z _
  exact (gappedGeometricDenominator_analytic z).meromorphicAt.inv

theorem gappedGeometricPole_exp (n : ℤ) :
    Complex.exp (gappedGeometricPole n) = 1 / 2 := by
  unfold gappedGeometricPole
  rw [Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), Complex.exp_int_mul,
    Complex.exp_two_pi_mul_I]
  norm_num

theorem gappedGeometricPole_denominator (n : ℤ) :
    2 * Complex.exp (gappedGeometricPole n) - 1 = 0 := by
  rw [gappedGeometricPole_exp]
  norm_num

theorem gappedGeometricPole_im (n : ℤ) :
    (gappedGeometricPole n).im = (n : ℝ) * (2 * Real.pi) := by
  simp only [gappedGeometricPole, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
    Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re]
  norm_num

theorem gappedGeometricPole_nonreal {n : ℤ} (hn : n ≠ 0) :
    (gappedGeometricPole n).im ≠ 0 := by
  rw [gappedGeometricPole_im]
  exact mul_ne_zero (Int.cast_ne_zero.mpr hn) (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem gappedGeometricPole_mem_slitPlane {n : ℤ} (hn : n ≠ 0) :
    gappedGeometricPole n ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (gappedGeometricPole_nonreal hn))

theorem gappedGeometricPole_denominator_hasDerivAt (n : ℤ) :
    HasDerivAt (fun z : ℂ => 2 * Complex.exp z - 1) 1 (gappedGeometricPole n) := by
  have hh := ((Complex.hasDerivAt_exp (gappedGeometricPole n)).const_mul (2 : ℂ)).sub_const 1
  convert hh using 1
  norm_num [gappedGeometricPole_exp]

theorem gappedGeometricPole_denominator_order_ne_top (n : ℤ) :
    analyticOrderAt (fun z : ℂ => 2 * Complex.exp z - 1) (gappedGeometricPole n) ≠ ⊤ := by
  intro hh
  have hz := analyticOrderAt_eq_top.mp hh
  have hd : HasDerivAt (fun z : ℂ => 2 * Complex.exp z - 1) 0 (gappedGeometricPole n) :=
    (hasDerivAt_const (gappedGeometricPole n) (0 : ℂ)).congr_of_eventuallyEq hz
  have hc := hd.unique (gappedGeometricPole_denominator_hasDerivAt n)
  norm_num at hc

theorem gappedGeometricPole_order_negative (n : ℤ) :
    meromorphicOrderAt gappedGeometricContinuation (gappedGeometricPole n) < 0 := by
  have ha := gappedGeometricDenominator_analytic (gappedGeometricPole n)
  have hnz : analyticOrderAt (fun z : ℂ => 2 * Complex.exp z - 1)
      (gappedGeometricPole n) ≠ 0 :=
    ha.analyticOrderAt_ne_zero.mpr (gappedGeometricPole_denominator n)
  lift analyticOrderAt (fun z : ℂ => 2 * Complex.exp z - 1) (gappedGeometricPole n)
    to ℕ using gappedGeometricPole_denominator_order_ne_top n with k hk
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    exact hnz (by rw [hkzero]; rfl)
  change meromorphicOrderAt ((fun z : ℂ => 2 * Complex.exp z - 1)⁻¹)
    (gappedGeometricPole n) < 0
  rw [meromorphicOrderAt_inv, ha.meromorphicOrderAt_eq, ← hk]
  rw [ENat.map_coe, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
  exact_mod_cast (neg_neg_of_pos (show (0 : ℤ) < k by exact_mod_cast hkpos))

theorem gappedGeometricPole_not_analytic (n : ℤ) :
    ¬ AnalyticAt ℂ gappedGeometricContinuation (gappedGeometricPole n) := by
  intro ha
  exact (not_le_of_gt (gappedGeometricPole_order_negative n)) ha.meromorphicOrderAt_nonneg

theorem gappedGeometricContinuation_not_analyticOnNhd_slitPlane :
    ¬ AnalyticOnNhd ℂ gappedGeometricContinuation Complex.slitPlane := by
  intro hh
  exact gappedGeometricPole_not_analytic 1
    (hh _ (gappedGeometricPole_mem_slitPlane (by norm_num : (1 : ℤ) ≠ 0)))

end UV
