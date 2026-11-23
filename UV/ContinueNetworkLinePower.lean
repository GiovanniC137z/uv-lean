import UV.ContinueNetworkDirectionalObstructions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Necessary directional power counting on a genuine momentum line.
A nonzero numerator coefficient of degree n costs n powers on that line. -/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators InnerProductSpace Polynomial

namespace UV

private theorem directionalPolynomial_eventually_leading_lower (U : ℝ[X]) {n : ℕ}
    (hU : U.coeff n ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop, c * t ^ n ≤ |U.eval t| := by
  have hn := Polynomial.le_natDegree_of_ne_zero hU
  have h0 : U ≠ 0 := fun h => hU (by simp [h])
  have hL := abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr h0)
  obtain ⟨A, hA, he⟩ := U.isEquivalent_atTop_lead.isBigO_symm.exists_pos
  refine ⟨|U.leadingCoeff| / A, div_pos hL hA, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), he.bound] with t ht hb
  have htn : 0 ≤ t := zero_le_one.trans ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg htn] at hb
  have hl := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hn) hL.le
  calc
    _ = (|U.leadingCoeff| * t ^ n) / A := by ring
    _ ≤ _ := (div_le_iff₀ hA).mpr ((hl.trans hb).trans_eq (mul_comm A _))

private theorem directionalMassiveFactor_line_lower {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {ν : ℝ} (hν : 0 ≤ ν)
    (x u : V) {t : ℝ} (ht : 1 ≤ t) :
    ((2 * (1 + ‖x‖ ^ 2)) ^ (-ν) * directionalMassiveFactor ν u) *
      t ^ (-(2 * ν)) ≤ directionalMassiveFactor ν (x + t • u) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hs : 1 + ‖t • u‖ ^ 2 ≤ (1 + ‖u‖ ^ 2) * t ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg ht0.le, mul_pow, add_mul, one_mul, mul_comm (‖u‖ ^ 2)]
    exact add_le_add_right (one_le_pow₀ ht) _
  have hp : directionalMassiveFactor ν u * t ^ (-(2 * ν)) ≤
      directionalMassiveFactor ν (t • u) := by
    unfold directionalMassiveFactor
    have he : -(2 * ν) = ((2 : ℕ) : ℝ) * (-ν) := by push_cast; ring
    rw [he, Real.rpow_natCast_mul ht0.le, ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hs (neg_nonpos.mpr hν)
  have hShift := (directionalMassiveFactor_shift_compare hν (t • u) x).1
  rw [add_comm (t • u) x] at hShift
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans hShift

private theorem directionalPower_exponent_of_integrable {f : ℝ → ℝ} {c a : ℝ}
    (hc : 0 < c) (h : ∀ᶠ t : ℝ in atTop, c * t ^ a ≤ f t) (hf : Integrable f) :
    a < -1 := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 h
  let T := max R 1
  have hT : 0 < T := zero_lt_one.trans_le (le_max_right _ _)
  have hI : IntegrableOn (fun t : ℝ => t ^ a) (Ioi T) := by
    have hJ : IntegrableOn (fun t : ℝ => c * t ^ a) (Ioi T) := by
      apply (hf.integrableOn (s := Ioi T)).mono'
      · exact (measurable_const.mul (measurable_id.pow_const _)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := hT.trans ht
      rw [Real.norm_of_nonneg (mul_nonneg hc.le (Real.rpow_nonneg ht0.le _))]
      exact hR t ((le_max_left _ _).trans ht.le)
    have hG : Integrable (fun t : ℝ => c⁻¹ * (c * t ^ a)) (volume.restrict (Ioi T)) :=
      hJ.const_mul c⁻¹
    apply hG.congr
    filter_upwards with t
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  exact (integrableOn_Ioi_rpow_iff hT).mp hI

variable {E : Type*} [Fintype E] {d : ℕ}
variable {V : E → Type*} [∀ e, NormedAddCommGroup (V e)] [∀ e, NormedSpace ℝ (V e)]

/-- On a parallel line in the kernel, only the factors indexed by S
can supply decay. A polynomial ray lower bound of degree n requires
strict power greater than n+1, including exclusion of equality. -/
theorem directionalAbsoluteModel_line_power_of_integrable
    (Q : DirectionalMomentum (d + 1) →L[ℝ] DirectionalMomentum (d + 1))
    (h : DirectionalMomentum (d + 1))
    (C : ∀ e, DirectionalMomentum (d + 1) →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (hν : ∀ e, 0 ≤ ν e) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k))
    (S : Finset E) (x u : DirectionalMomentum (d + 1))
    (hQ : Q u = 0) (hh : inner ℝ h u = 0) (hC : ∀ e ∉ S, C e u = 0)
    (n : ℕ) {c : ℝ} (hc : 0 < c)
    (hP : ∀ᶠ t : ℝ in atTop, c * t ^ n ≤ ‖directionalNumerator P (x + t • u)‖)
    (hI : Integrable (fun t : ℝ => directionalAbsoluteModel Q h C p ν P (x + t • u))) :
    1 + (n : ℝ) < ∑ e ∈ S, 2 * ν e := by
  classical
  let s (e : E) : ℝ := if e ∈ S then 2 * ν e else 0
  let N := ∑ e, s e
  let a (e : E) : ℝ := if e ∈ S then
    (2 * (1 + ‖C e x + p e‖ ^ 2)) ^ (-ν e) * directionalMassiveFactor (ν e) (C e u)
    else directionalMassiveFactor (ν e) (C e x + p e)
  let A := ∏ e, a e
  let Z := Real.exp (-inner ℝ x (Q x) + inner ℝ h x)
  have hA : 0 < A := Finset.prod_pos fun e _ => by
    unfold a
    split
    · exact mul_pos (by positivity) (directionalMassiveFactor_pos _ _)
    · exact directionalMassiveFactor_pos _ _
  have hZ : 0 < Z := Real.exp_pos _
  have hg : ∀ᶠ t : ℝ in atTop, (c * Z * A) * t ^ ((n : ℝ) - N) ≤
      directionalAbsoluteModel Q h C p ν P (x + t • u) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hP] with t ht hp
    have ht0 : 0 < t := zero_lt_one.trans_le ht
    have hlower : A * t ^ (-N) ≤
        ∏ e, directionalMassiveFactor (ν e) (C e (x + t • u) + p e) := by
      have hN : -N = ∑ e, -(s e) := by simp [N]
      rw [hN, Real.rpow_sum_of_pos ht0, ← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod
      · intro e _
        apply mul_nonneg
        · unfold a
          split
          · exact mul_nonneg (by positivity) (directionalMassiveFactor_pos _ _).le
          · exact (directionalMassiveFactor_pos _ _).le
        · exact Real.rpow_nonneg ht0.le _
      · intro e _
        by_cases he : e ∈ S
        · have hre : C e (x + t • u) + p e = (C e x + p e) + t • C e u := by
            simp only [map_add, map_smul, add_right_comm]
          rw [hre]
          simpa only [a, s, if_pos he] using
            directionalMassiveFactor_line_lower (hν e) (C e x + p e) (C e u) ht
        · simp [a, s, he, hC e he]
    have hux : inner ℝ u (Q x) = 0 := by rw [hSym, hQ, inner_zero_right]
    have hline : directionalAbsoluteModel Q h C p ν P (x + t • u) =
        ‖directionalNumerator P (x + t • u)‖ * Z *
          ∏ e, directionalMassiveFactor (ν e) (C e (x + t • u) + p e) := by
      simp only [directionalAbsoluteModel, Z]
      congr 2
      simp [map_add, map_smul, hQ, real_inner_smul_left, real_inner_smul_right, hux, hh,
        inner_add_left, inner_add_right]
    rw [hline]
    calc
      _ = c * t ^ n * Z * (A * t ^ (-N)) := by
        rw [sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_natCast]
        ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hp hZ.le) hlower
        (by positivity) (by positivity)
  have hstrict := directionalPower_exponent_of_integrable (mul_pos (mul_pos hc hZ) hA) hg hI
  have hN : N = ∑ e ∈ S, 2 * ν e := by
    simp only [N, s, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  linarith

private theorem directionalRay_mul_coordinate_coeff_continuous {d : ℕ}
    (R : DirectionalMomentum d → ℝ[X])
    (hR : ∀ n, Continuous (fun x => (R x).coeff n))
    (u : DirectionalMomentum d) (i : Fin d) (n : ℕ) :
    Continuous (fun x => (R x *
      (Polynomial.C (x i) + Polynomial.C (u i) * Polynomial.X)).coeff n) := by
  cases n with
  | zero =>
      simp only [mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_C,
        Polynomial.coeff_mul_X_zero, add_zero]
      exact (hR 0).mul (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)
  | succ n =>
      simp only [mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X,
        Polynomial.coeff_mul_C]
      exact ((hR (n + 1)).mul (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)).add
        ((hR n).mul continuous_const)

/-- The actual real and imaginary ray polynomials have coefficients
continuous in the ray base point. -/
theorem directionalNumerator_ray_continuous_coefficients {d : ℕ}
    (P : MvPolynomial (Fin d) ℂ) (u : DirectionalMomentum d) :
    ∃ R I : DirectionalMomentum d → ℝ[X],
      (∀ n, Continuous (fun x => (R x).coeff n)) ∧
      (∀ n, Continuous (fun x => (I x).coeff n)) ∧
      ∀ x (t : ℝ), (directionalNumerator P (x + t • u)).re = (R x).eval t ∧
        (directionalNumerator P (x + t • u)).im = (I x).eval t := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      exact ⟨fun _ => Polynomial.C a.re, fun _ => Polynomial.C a.im,
        fun _ => continuous_const, fun _ => continuous_const,
        fun _ _ => by simp [directionalNumerator]⟩
  | add p q hp hq =>
      obtain ⟨Rp, Ip, hRp, hIp, hp⟩ := hp
      obtain ⟨Rq, Iq, hRq, hIq, hq⟩ := hq
      refine ⟨fun x => Rp x + Rq x, fun x => Ip x + Iq x, ?_, ?_, fun x t => ?_⟩
      · intro n
        simpa only [Polynomial.coeff_add] using (hRp n).add (hRq n)
      · intro n
        simpa only [Polynomial.coeff_add] using (hIp n).add (hIq n)
      · simp only [directionalNumerator, map_add, Complex.add_re, Complex.add_im,
          Polynomial.eval_add, ← (hp x t).1, ← (hp x t).2, ← (hq x t).1, ← (hq x t).2]
        exact ⟨trivial, trivial⟩
  | mul_X p i hp =>
      obtain ⟨R, I, hR, hI, hp⟩ := hp
      let A (x : DirectionalMomentum d) := Polynomial.C (x i) + Polynomial.C (u i) * Polynomial.X
      refine ⟨fun x => R x * A x, fun x => I x * A x,
        directionalRay_mul_coordinate_coeff_continuous R hR u i,
        directionalRay_mul_coordinate_coeff_continuous I hI u i, fun x t => ?_⟩
      have hA : (A x).eval t = (x + t • u) i := by
        simp only [A, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
          Polynomial.eval_X, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [Polynomial.eval_mul, Polynomial.eval_mul, hA, ← (hp x t).1, ← (hp x t).2]
      simp [directionalNumerator, Complex.mul_re, Complex.mul_im]

/-- One nonzero coefficient of degree n on an actual orthonormal fiber
persists on an open set of transverse fibers. The full momentum
integral then requires strict one-dimensional power counting. -/
theorem directionalAbsoluteModel_one_dimensional_power_necessary
    (Q : DirectionalMomentum (d + 1) →L[ℝ] DirectionalMomentum (d + 1))
    (h : DirectionalMomentum (d + 1))
    (C : ∀ e, DirectionalMomentum (d + 1) →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (hν : ∀ e, 0 ≤ ν e) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k)) (S : Finset E)
    (b : OrthonormalBasis (Fin (d + 1)) ℝ (DirectionalMomentum (d + 1)))
    (hQ : Q (b 0) = 0) (hh : inner ℝ h (b 0) = 0)
    (hC : ∀ e ∉ S, C e (b 0) = 0)
    (n : ℕ)
    (hmark : ∃ (y : Fin d → ℝ) (A : ℝ[X]), A.coeff n ≠ 0 ∧
      ((∀ t : ℝ, (directionalNumerator P (directionalFiber b t y)).re = A.eval t) ∨
        (∀ t : ℝ, (directionalNumerator P (directionalFiber b t y)).im = A.eval t)))
    (hI : Integrable (directionalAbsoluteModel Q h C p ν P)) :
    1 + (n : ℝ) < ∑ e ∈ S, 2 * ν e := by
  obtain ⟨R, I, hR, hIm, heval⟩ := directionalNumerator_ray_continuous_coefficients P (b 0)
  let x := directionalFiber b 0
  have hae := directionalFiber_integrable_ae b hI
  have hmark' : ∃ y, (R (x y)).coeff n ≠ 0 ∨ (I (x y)).coeff n ≠ 0 := by
    obtain ⟨y, A, hn, he | he⟩ := hmark
    · refine ⟨y, Or.inl ?_⟩
      have hEq : R (x y) = A := Polynomial.funext fun t => by
        rw [← (heval (x y) t).1, ← directionalFiber_affine b t y]
        exact he t
      rwa [hEq]
    · refine ⟨y, Or.inr ?_⟩
      have hEq : I (x y) = A := Polynomial.funext fun t => by
        rw [← (heval (x y) t).2, ← directionalFiber_affine b t y]
        exact he t
      rwa [hEq]
  let U : Set (Fin d → ℝ) := {y | (R (x y)).coeff n ≠ 0 ∨ (I (x y)).coeff n ≠ 0}
  have hx : Continuous x := directionalFiber_continuous_transverse b 0
  have hU : IsOpen U := (isOpen_ne_fun ((hR n).comp hx) continuous_const).union
    (isOpen_ne_fun ((hIm n).comp hx) continuous_const)
  have hpos : 0 < volume U := hU.measure_pos volume hmark'
  obtain ⟨y, hy, hIy⟩ := ((frequently_ae_mem_iff.2 hpos.ne').and_eventually hae).exists
  have hy' : (R (x y)).coeff n ≠ 0 ∨ (I (x y)).coeff n ≠ 0 := hy
  have hIy' : Integrable (fun t : ℝ =>
      directionalAbsoluteModel Q h C p ν P (x y + t • b 0)) := by
    convert hIy using 1
    ext t
    rw [directionalFiber_affine b t y]
  have hbound : ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop,
      c * t ^ n ≤ ‖directionalNumerator P (x y + t • b 0)‖ := by
    rcases hy' with hy' | hy'
    · obtain ⟨c, hc, hb⟩ := directionalPolynomial_eventually_leading_lower (R (x y)) hy'
      refine ⟨c, hc, hb.mono fun t ht => ht.trans ?_⟩
      rw [← (heval (x y) t).1]
      exact Complex.abs_re_le_norm _
    · obtain ⟨c, hc, hb⟩ := directionalPolynomial_eventually_leading_lower (I (x y)) hy'
      refine ⟨c, hc, hb.mono fun t ht => ht.trans ?_⟩
      rw [← (heval (x y) t).2]
      exact Complex.abs_im_le_norm _
  obtain ⟨c, hc, hbound⟩ := hbound
  exact directionalAbsoluteModel_line_power_of_integrable Q h C p ν hν P hSym S (x y)
    (b 0) hQ hh hC n hc hbound hIy'

/-- The degree witness can be supplied at any base point of a unit
line. Translating its parameter to the orthonormal fiber preserves that
degree, so equality of the one-dimensional count forces divergence. -/
theorem directionalAbsoluteModel_unit_ray_power_necessary
    (Q : DirectionalMomentum (d + 1) →L[ℝ] DirectionalMomentum (d + 1))
    (h : DirectionalMomentum (d + 1))
    (C : ∀ e, DirectionalMomentum (d + 1) →L[ℝ] V e) (p : ∀ e, V e)
    (ν : E → ℝ) (hν : ∀ e, 0 ≤ ν e) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (hSym : ∀ k k', inner ℝ k (Q k') = inner ℝ k' (Q k)) (S : Finset E)
    (u : DirectionalMomentum (d + 1)) (hu : ‖u‖ = 1)
    (hQ : Q u = 0) (hh : inner ℝ h u = 0) (hC : ∀ e ∉ S, C e u = 0)
    (x : DirectionalMomentum (d + 1)) (A : ℝ[X]) (hA : A ≠ 0)
    (hmark : (∀ t : ℝ, (directionalNumerator P (x + t • u)).re = A.eval t) ∨
      (∀ t : ℝ, (directionalNumerator P (x + t • u)).im = A.eval t))
    (hI : Integrable (directionalAbsoluteModel Q h C p ν P)) :
    1 + (A.natDegree : ℝ) < ∑ e ∈ S, 2 * ν e := by
  obtain ⟨b, hb⟩ := directional_basis_with_unit u hu
  let t₀ := b.repr x 0
  let y : Fin d → ℝ := fun j => b.repr x j.succ
  have hxy : directionalFiber b t₀ y = x := by
    apply b.repr.injective
    rw [directionalFiber, LinearIsometryEquiv.apply_symm_apply]
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [t₀, y]
  have hline (t : ℝ) : directionalFiber b t y = x + (t - t₀) • u := by
    calc
      _ = directionalFiber b 0 y + t • u := by rw [directionalFiber_affine, hb]
      _ = (directionalFiber b 0 y + t₀ • u) + (t - t₀) • u := by
        rw [add_assoc, ← add_smul, show t₀ + (t - t₀) = t by ring]
      _ = _ := by rw [← hb, ← directionalFiber_affine, hxy, hb]
  let B := A.comp (Polynomial.X - Polynomial.C t₀)
  have hBdeg : B.natDegree = A.natDegree := by
    simp only [B, Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
  have hBval (t : ℝ) : B.eval t = A.eval (t - t₀) := by simp [B]
  have hB : B ≠ 0 := by
    intro hz
    apply hA
    apply Polynomial.funext
    intro t
    have hval := hBval (t + t₀)
    rw [hz, Polynomial.eval_zero, add_sub_cancel_right] at hval
    simpa only [Polynomial.eval_zero] using hval.symm
  apply directionalAbsoluteModel_one_dimensional_power_necessary Q h C p ν hν P hSym S b
    (by rwa [hb]) (by rwa [hb]) (by rwa [hb]) A.natDegree ?_ hI
  refine ⟨y, B, ?_, ?_⟩
  · rw [← hBdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hB
  · rcases hmark with hre | him
    · exact Or.inl fun t => by rw [hline t, hBval, hre]
    · exact Or.inr fun t => by rw [hline t, hBval, him]

end UV
