import UV.FurtherCurvatureShell
import UV.Convergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The literal weighted torus line estimate of (UV, eq:uvpeC-line-estimate).
All momenta still belong to the stated fixed sector-plane torus. -/

noncomputable section

open Filter Real
open scoped BigOperators Topology

namespace UV.FurtherCurvatureLine

open UV.FurtherCurvatureShell
open UV.RevisionCurvatureDeterminant (latticeFrequency)

def curvatureCovariance (ℓ : ℝ) (k : TorusMode) : ℝ :=
  ((latticeFrequency k)^2 * (1 + exp (-2*ℓ*latticeFrequency k)))⁻¹

def curvatureLine (ℓ : ℝ) (k : TorusMode) : ℝ :=
  exp (-2*ℓ*latticeFrequency k) * curvatureCovariance ℓ k

def weightedLine (s ℓ : ℝ) (k : TorusMode) : ℝ :=
  (1 + latticeFrequency k)^s * curvatureLine ℓ k

def effectiveRadius (Λ ℓ : ℝ) : ℝ :=
  if ℓ = 0 then Λ else min Λ ℓ⁻¹

theorem weightedLine_nonneg (s ℓ : ℝ) (k : TorusMode) : 0 ≤ weightedLine s ℓ k := by
  have hk : 0 ≤ latticeFrequency k := sqrt_nonneg _
  unfold weightedLine curvatureLine curvatureCovariance
  positivity

@[simp] theorem weightedLine_zero (s ℓ : ℝ) : weightedLine s ℓ 0 = 0 := by
  simp [weightedLine, curvatureLine, curvatureCovariance, latticeFrequency]

private theorem shell_pointwise {s ℓ : ℝ} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (j : ℕ)
    {k : TorusMode} (hk : k ∈ modeShell j) :
    weightedLine s ℓ k ≤ 3^s * ((j+1 : ℕ) : ℝ)^s *
      (((j+1 : ℕ) : ℝ)^2)⁻¹ * exp (-2*ℓ*((j+1 : ℕ) : ℝ)) := by
  let m : ℝ := ((j+1 : ℕ) : ℝ)
  let r := latticeFrequency k
  have hm : 0 < m := by positivity
  have hm1 : 1 ≤ m := by simp [m]
  have he : latticeHeight k = j+1 := mem_modeShell.mp hk
  have hl : m ≤ r := by simpa only [m, r, he] using latticeHeight_le_latticeFrequency k
  have hu : r ≤ 2*m := by simpa only [m, r, he] using latticeFrequency_le_twice_height k
  have hr : 0 < r := hm.trans_le hl
  have h1 : (1+r)^s ≤ 3^s * m^s := by
    rw [← Real.mul_rpow (by norm_num : 0 ≤ (3 : ℝ)) hm.le]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hs
  have h2 : (r^2 * (1+exp (-2*ℓ*r)))⁻¹ ≤ (m^2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    have hgrow : m^2 ≤ r^2 := pow_le_pow_left₀ hm.le hl _
    refine hgrow.trans (le_mul_of_one_le_right (sq_nonneg _) ?_)
    linarith [exp_nonneg (-2*ℓ*r)]
  have h3 : exp (-2*ℓ*r) ≤ exp (-2*ℓ*m) := by
    apply exp_le_exp.mpr
    nlinarith [mul_nonneg hℓ (sub_nonneg.mpr hl)]
  calc
    weightedLine s ℓ k = (1+r)^s * (r^2*(1+exp (-2*ℓ*r)))⁻¹ * exp (-2*ℓ*r) := by
      unfold weightedLine curvatureLine curvatureCovariance r
      ring
    _ ≤ _ := by gcongr

theorem weighted_shell_bound {s ℓ : ℝ} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) (j : ℕ) :
    ∑ k ∈ modeShell j, weightedLine s ℓ k ≤
      (80 * 3^s) * ((j+1 : ℕ) : ℝ)^(1+s) * exp (-2*ℓ*((j+1 : ℕ) : ℝ)) := by
  let m : ℝ := ((j+1 : ℕ) : ℝ)
  have hm : 0 < m := by positivity
  calc
    _ ≤ ∑ _k ∈ modeShell j, 3^s * m^s * (m^2)⁻¹ * exp (-2*ℓ*m) :=
      Finset.sum_le_sum (fun _ hk => shell_pointwise hs hℓ j hk)
    _ = ((modeShell j).card : ℝ) * (3^s * m^s * (m^2)⁻¹ * exp (-2*ℓ*m)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (80 * m^3) * (3^s * m^s * (m^2)⁻¹ * exp (-2*ℓ*m)) :=
      mul_le_mul_of_nonneg_right (modeShell_card j) (by positivity)
    _ = _ := by
      change _ = (80 * 3^s) * m ^ ((1:ℝ)+s) * exp (-2*ℓ*m)
      rw [Real.rpow_add hm, Real.rpow_one]
      field_simp

private theorem sum_le_shell_range {s ℓ Λ : ℝ} (hs : 0 ≤ s) (hℓ : 0 ≤ ℓ) :
    ∑ k ∈ sphericalModes Λ, weightedLine s ℓ k ≤
      (80 * 3^s) * ∑ j ∈ Finset.range ⌊Λ⌋₊,
        ((j+1 : ℕ) : ℝ)^(1+s) * exp (-2*ℓ*((j+1 : ℕ) : ℝ)) := by
  classical
  have hmaps (k) (hk : k ∈ sphericalModes Λ) :
      latticeHeight k - 1 ∈ Finset.range ⌊Λ⌋₊ := by
    have hf := mem_sphericalModes.mp hk
    have hpos := latticeHeight_ne_zero hf.1
    have hle := Nat.le_floor ((latticeHeight_le_latticeFrequency k).trans hf.2)
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (weightedLine s ℓ), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => weightedLine_nonneg s ℓ k)).trans
    (by simpa only [mul_assoc] using weighted_shell_bound hs hℓ j)
  intro k hk
  obtain ⟨hm, hh⟩ := Finset.mem_filter.mp hk
  have hpos := latticeHeight_ne_zero (mem_sphericalModes.mp hm).1
  exact mem_modeShell.mpr (by omega)

private theorem power_cutoff {p Λ ℓ : ℝ} (hp : 0 ≤ p) (hΛ : 0 ≤ Λ) (hℓ : 0 ≤ ℓ) :
    ∑ j ∈ Finset.range ⌊Λ⌋₊, ((j+1 : ℕ) : ℝ)^p *
      exp (-2*ℓ*((j+1 : ℕ) : ℝ)) ≤ (1+Λ)^(p+1) := by
  have hfloor : (⌊Λ⌋₊ : ℝ) ≤ Λ := Nat.floor_le hΛ
  calc
    _ ≤ ∑ _j ∈ Finset.range ⌊Λ⌋₊, (1+Λ)^p := by
      apply Finset.sum_le_sum
      intro j hj
      have hm : ((j+1 : ℕ) : ℝ) ≤ (⌊Λ⌋₊ : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      have he : exp (-2*ℓ*((j+1 : ℕ) : ℝ)) ≤ 1 := by
        apply exp_le_one_iff.mpr
        have haux : 0 ≤ 2*ℓ*((j+1 : ℕ) : ℝ) := by positivity
        ring_nf at haux ⊢
        linarith
      refine (mul_le_of_le_one_right (by positivity) he).trans ?_
      exact Real.rpow_le_rpow (by positivity) (by linarith) hp
    _ = (⌊Λ⌋₊ : ℝ) * (1+Λ)^p := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ ≤ (1+Λ) * (1+Λ)^p := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by rw [Real.rpow_add (by positivity), Real.rpow_one, mul_comm]

private theorem geometric_cutoff {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    ∑ j ∈ Finset.range N, exp (-ℓ * ((j+1 : ℕ) : ℝ)) ≤ ℓ⁻¹ := by
  have hterm (j : ℕ) :
      ℓ * exp (-ℓ * ((j+1 : ℕ) : ℝ)) ≤
        exp (-ℓ * (j : ℝ)) - exp (-ℓ * ((j+1 : ℕ) : ℝ)) := by
    have hp := mul_le_mul_of_nonneg_right (Real.add_one_le_exp ℓ)
      (exp_nonneg (-ℓ* ((j+1 : ℕ) : ℝ)))
    rw [← Real.exp_add] at hp
    have he : ℓ + -ℓ * ((j+1 : ℕ) : ℝ) = -ℓ * (j : ℝ) := by push_cast; ring
    rw [he] at hp
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j _ => hterm j)
  rw [← Finset.mul_sum] at hsum
  have htelescope :
      (∑ j ∈ Finset.range N, (exp (-ℓ * (j:ℝ)) - exp (-ℓ * ((j+1 : ℕ) : ℝ)))) =
        1 - exp (-ℓ * (N:ℝ)) := by
    clear hsum
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  rw [htelescope] at hsum
  have hb : ℓ * ∑ j ∈ Finset.range N, exp (-ℓ * ((j+1 : ℕ) : ℝ)) ≤ 1 :=
    hsum.trans (sub_le_self _ (exp_nonneg _))
  rw [← one_div]
  apply (le_div_iff₀ hℓ).mpr
  simpa only [mul_comm] using hb

private theorem power_damping {p ℓ : ℝ} (hp : 0 ≤ p) (hℓ : 0 < ℓ)
    (q : ℕ) (hq : p ≤ (q : ℝ)) (N : ℕ) :
    ∑ j ∈ Finset.range N, ((j+1 : ℕ) : ℝ)^p *
      exp (-2*ℓ*((j+1 : ℕ) : ℝ)) ≤
      ((q.factorial : ℝ) * exp 1) * (1+ℓ⁻¹)^(p+1) := by
  let A := (q.factorial : ℝ) * exp 1
  have hscale : 0 < 1 + ℓ⁻¹ := by positivity
  have hterm (j : ℕ) : ((j+1 : ℕ) : ℝ)^p * exp (-2*ℓ*((j+1 : ℕ) : ℝ)) ≤
      A * (1+ℓ⁻¹)^p * exp (-ℓ*((j+1 : ℕ) : ℝ)) := by
    let m : ℝ := ((j+1 : ℕ) : ℝ)
    have hm : 0 < m := by positivity
    have hx : 1 ≤ 1+ℓ*m := by nlinarith
    have hprod : m ≤ (1+ℓ⁻¹)*(1+ℓ*m) := by
      rw [add_mul, one_mul, mul_add, mul_one, ← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul]
      linarith [inv_nonneg.mpr hℓ.le]
    have hpow : m^p ≤ (1+ℓ⁻¹)^p * (1+ℓ*m)^(q : ℝ) := by
      calc
        _ ≤ ((1+ℓ⁻¹)*(1+ℓ*m))^p := Real.rpow_le_rpow hm.le hprod hp
        _ = (1+ℓ⁻¹)^p * (1+ℓ*m)^p := Real.mul_rpow hscale.le (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx hq) (by positivity)
    have hfact := UV.pow_mul_exp_neg_le (show (0:ℝ) < 1 by norm_num)
      (show 0 ≤ 1+ℓ*m by positivity) q
    simp only [one_mul, one_pow, div_one] at hfact
    have hxpow : (1+ℓ*m)^(q : ℝ) * exp (-ℓ*m) ≤ A := by
      rw [Real.rpow_natCast, show -ℓ*m = -(1+ℓ*m)+1 by ring, Real.exp_add, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hfact (exp_nonneg 1)
    change m^p * exp (-2*ℓ*m) ≤ A * (1+ℓ⁻¹)^p * exp (-ℓ*m)
    rw [show -2*ℓ*m = -ℓ*m + -ℓ*m by ring, Real.exp_add]
    calc
      _ ≤ ((1+ℓ⁻¹)^p * (1+ℓ*m)^(q : ℝ)) * (exp (-ℓ*m) * exp (-ℓ*m)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (1+ℓ⁻¹)^p * ((1+ℓ*m)^(q : ℝ) * exp (-ℓ*m)) * exp (-ℓ*m) := by ring
      _ ≤ _ := by rw [mul_comm A]; gcongr
  calc
    _ ≤ A * (1+ℓ⁻¹)^p * ∑ j ∈ Finset.range N, exp (-ℓ*((j+1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => hterm j)
    _ ≤ A * (1+ℓ⁻¹)^p * ℓ⁻¹ :=
      mul_le_mul_of_nonneg_left (geometric_cutoff hℓ N) (by positivity)
    _ ≤ A * (1+ℓ⁻¹)^p * (1+ℓ⁻¹) := by gcongr; linarith
    _ = _ := by rw [Real.rpow_add hscale, Real.rpow_one, mul_assoc]

/-- The source's uniform line estimate, including the cutoff at depth zero
and every real exponent s ≥ 0. -/
theorem spherical_weighted_line_bound {s : ℝ} (hs : 0 ≤ s) :
    ∃ C > 0, ∀ {Λ ℓ : ℝ}, 0 ≤ Λ → 0 ≤ ℓ →
      ∑ k ∈ sphericalModes Λ, weightedLine s ℓ k ≤ C * (1+effectiveRadius Λ ℓ)^(2+s) := by
  obtain ⟨q, hq⟩ := exists_nat_ge (1+s)
  let A : ℝ := max 1 ((q.factorial : ℝ) * exp 1)
  have hA : 1 ≤ A := le_max_left _ _
  have hpos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨(80 * 3^s) * A, by positivity, ?_⟩
  intro Λ ℓ hΛ hℓ
  have hstart := sum_le_shell_range hs hℓ (Λ := Λ)
  have hpow := power_cutoff (p := 1+s) (by linarith) hΛ hℓ
  have hexp : 1+s+1 = 2+s := by ring
  rw [hexp] at hpow
  have hpoly : ∑ k ∈ sphericalModes Λ, weightedLine s ℓ k ≤
      (80 * 3^s) * A * (1+Λ)^(2+s) := by
    calc
      _ ≤ (80 * 3^s) * (1+Λ)^(2+s) :=
        hstart.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ ≤ _ := by
        have hc : 80*(3:ℝ)^s ≤ 80*3^s*A := le_mul_of_one_le_right (by positivity) hA
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  by_cases hzero : ℓ = 0
  · simpa only [effectiveRadius, if_pos hzero] using hpoly
  by_cases hcut : Λ ≤ ℓ⁻¹
  · simpa only [effectiveRadius, if_neg hzero, min_eq_left hcut] using hpoly
  have hℓp : 0 < ℓ := lt_of_le_of_ne hℓ (Ne.symm hzero)
  have hdamp := power_damping (p := 1+s) (by linarith) hℓp q hq ⌊Λ⌋₊
  rw [hexp] at hdamp
  rw [effectiveRadius, if_neg hzero, min_eq_right (le_of_not_ge hcut)]
  refine hstart.trans ((mul_le_mul_of_nonneg_left hdamp (by positivity)).trans ?_)
  rw [← mul_assoc]
  gcongr
  exact le_max_right _ _

private theorem sum_le_spherical_sum (modes : Finset TorusMode) (s ℓ : ℝ) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∑ k ∈ modes, weightedLine s ℓ k ≤
      ∑ k ∈ sphericalModes Λ, weightedLine s ℓ k := by
  classical
  let Λ := ∑ k ∈ modes, latticeFrequency k
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg (fun _ _ => sqrt_nonneg _)
  refine ⟨Λ, hΛ, ?_⟩
  have hs : modes.erase 0 ⊆ sphericalModes Λ := by
    intro k hk
    obtain ⟨hn, hm⟩ := Finset.mem_erase.mp hk
    exact mem_sphericalModes.mpr
      ⟨hn, Finset.single_le_sum (f := latticeFrequency) (fun _ _ => sqrt_nonneg _) hm⟩
  have he : (∑ k ∈ modes.erase 0, weightedLine s ℓ k) =
      ∑ k ∈ modes, weightedLine s ℓ k := by
    by_cases h : 0 ∈ modes
    · simpa using Finset.sum_erase_add modes (weightedLine s ℓ) h
    · rw [Finset.erase_eq_of_notMem h]
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => weightedLine_nonneg s ℓ k)

/-- At positive depth the literal line is absolutely summable over all torus
modes, with the same effective-radius polynomial bound. -/
theorem full_weighted_line_bound {s : ℝ} (hs : 0 ≤ s) :
    ∃ C > 0, ∀ {ℓ : ℝ}, 0 < ℓ →
      Summable (weightedLine s ℓ) ∧
        ∑' k, weightedLine s ℓ k ≤ C * (1+ℓ⁻¹)^(2+s) := by
  obtain ⟨C, hC, hc⟩ := spherical_weighted_line_bound hs
  refine ⟨C, hC, fun {ℓ} hℓ => ?_⟩
  have hb (modes : Finset TorusMode) :
      ∑ k ∈ modes, weightedLine s ℓ k ≤ C * (1+ℓ⁻¹)^(2+s) := by
    obtain ⟨Λ, hΛ, hsph⟩ := sum_le_spherical_sum modes s ℓ
    refine hsph.trans ((hc hΛ hℓ.le).trans ?_)
    rw [effectiveRadius, if_neg hℓ.ne']
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.rpow_le_rpow
      (by have hmin := le_min hΛ (inv_nonneg.mpr hℓ.le); linarith)
      (by linarith [min_le_right Λ ℓ⁻¹]) (by linarith)
  have hsum := summable_of_sum_le (weightedLine_nonneg s ℓ) hb
  exact ⟨hsum, hsum.tsum_le_of_sum_le hb⟩

end UV.FurtherCurvatureLine
