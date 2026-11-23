import UV.ContinueOpticalRectangle
import UV.ContinueOpticalDirichlet

/-! Ultraviolet divergence of a gauge-invariant rectangular Wilson current
with independent Dirichlet normal noise. The zero spatial mode is omitted. -/

noncomputable section

open MeasureTheory Real Set Filter
open scoped BigOperators ENNReal Topology

namespace UV

abbrev OpticalMode := Fin 3 → ℤ

def opticalSpacing (L : ℝ) : ℝ := 2*π/L

def opticalRectModeVariance {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (y : ℝ) (n : OpticalMode) : ℝ :=
  opticalDirichletGreen ‖opticalTorusMode L n‖ y y *
    thinCurrentNormSq (opticalRectEdges hL hh) (opticalTorusMode L n)

theorem opticalRectModeVariance_zero {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (y : ℝ) :
    opticalRectModeVariance hL hh y 0 = 0 := by
  have h0 : opticalTorusMode L 0 = 0 := by ext j; fin_cases j <;> simp [opticalTorusMode]
  simp [opticalRectModeVariance, h0, opticalDirichletGreen]

theorem opticalRectModeVariance_nonneg {L h : ℝ} (hL : 0 < L) (hh : 0 < h)
    {y : ℝ} (hy : 0 ≤ y) (n : OpticalMode) : 0 ≤ opticalRectModeVariance hL hh y n := by
  unfold opticalRectModeVariance
  apply mul_nonneg _ (thinCurrentNormSq_nonneg _ _)
  rw [opticalDirichletGreen_diag]
  exact div_nonneg (sub_nonneg.mpr (exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))) (by positivity)

def opticalShellMode (N : ℕ) (ij : Fin N × Fin N) : OpticalMode :=
  ![0, 2*(ij.1.val:ℤ)+1, 4*(N:ℤ)+ij.2.val]

theorem opticalShellMode_injective (N : ℕ) : Function.Injective (opticalShellMode N) := by
  intro u v huv
  have h1 := congrFun huv 1
  have h2 := congrFun huv 2
  simp [opticalShellMode] at h1 h2
  apply Prod.ext <;> apply Fin.ext <;> omega

theorem opticalTorusMode_norm_sq (L : ℝ) (b c : ℤ) :
    ‖opticalTorusMode L ![0,b,c]‖^2 = opticalSpacing L ^ 2 * ((b:ℝ)^2 + (c:ℝ)^2) := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, opticalTorusMode, opticalSpacing, Real.norm_eq_abs]
  ring

theorem opticalShellMode_radius {L : ℝ} (hL : 0 < L) (N : ℕ) (ij : Fin N × Fin N) :
    let k := ‖opticalTorusMode L (opticalShellMode N ij)‖
    4 * opticalSpacing L * N ≤ k ∧ k ≤ 6 * opticalSpacing L * N := by
  have ha : 0 < opticalSpacing L := by unfold opticalSpacing; positivity
  let a := opticalSpacing L
  have hi : (ij.1.val : ℝ) + 1 ≤ N := by exact_mod_cast ij.1.isLt
  have hj : (ij.2.val : ℝ) ≤ N := by exact_mod_cast ij.2.isLt.le
  have hi0 : 0 ≤ (ij.1.val : ℝ) := Nat.cast_nonneg _
  have hj0 : 0 ≤ (ij.2.val : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have h1 := sq_le_sq₀ (by positivity : 0 ≤ 2*(ij.1.val:ℝ)+1) (by positivity : 0 ≤ 2*(N:ℝ))
  have h2 := sq_le_sq₀ (by positivity : 0 ≤ 4*(N:ℝ)+(ij.2.val:ℝ)) (by positivity : 0 ≤ 5*(N:ℝ))
  have h3 := sq_le_sq₀ (by positivity : 0 ≤ 4*(N:ℝ)) (by positivity : 0 ≤ 4*(N:ℝ)+(ij.2.val:ℝ))
  have htop : (2*(ij.1.val:ℝ)+1)^2 + (4*(N:ℝ)+(ij.2.val:ℝ))^2 ≤ (6*(N:ℝ))^2 := by
    nlinarith [h1.mpr (by linarith), h2.mpr (by linarith), sq_nonneg (N:ℝ)]
  have hd := opticalTorusMode_norm_sq L (2*(ij.1.val:ℤ)+1) (4*(N:ℤ)+ij.2.val)
  push_cast at hd
  change ‖opticalTorusMode L (opticalShellMode N ij)‖^2 =
    a^2 * ((2 * (ij.1.val:ℝ) + 1)^2 + (4 * (N:ℝ) + (ij.2.val:ℝ))^2) at hd
  change 4*a*N ≤ _ ∧ _ ≤ 6*a*N
  have ha0 : 0 ≤ a := ha.le
  constructor
  · apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [hd, show (4*a*(N:ℝ))^2 = a^2 * (4*(N:ℝ))^2 by ring]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    nlinarith [h3.mpr (by linarith), sq_nonneg (2*(ij.1.val:ℝ)+1)]
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [hd, show (6*a*(N:ℝ))^2 = a^2 * (6*(N:ℝ))^2 by ring]
    exact mul_le_mul_of_nonneg_left htop (sq_nonneg _)

/-- A quadratic number of distinct odd modes lies in every sufficiently
large open physical shell K < |p| < 2K. -/
theorem opticalRect_shell_family {L K : ℝ} (hL : 0 < L) (hK : 28 * opticalSpacing L < K) :
    ∃ N : ℕ, K/(4*opticalSpacing L) < N ∧
      ∀ ij : Fin N × Fin N, K < ‖opticalTorusMode L (opticalShellMode N ij)‖ ∧
        ‖opticalTorusMode L (opticalShellMode N ij)‖ < 2*K := by
  let a := opticalSpacing L
  have ha : 0 < a := by dsimp [a,opticalSpacing]; positivity
  have hk : 0 < K := by change 28*a < K at hK; linarith
  let N := ⌊2*K/(7*a)⌋₊
  have hf1 : (N:ℝ) ≤ 2*K/(7*a) := Nat.floor_le (by positivity)
  have hf2 : 2*K/(7*a) < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hu := (le_div_iff₀ (by positivity : 0 < 7*a)).mp hf1
  have hl := (div_lt_iff₀ (by positivity : 0 < 7*a)).mp hf2
  have hlo : K < 4*a*N := by change 28*a < K at hK; nlinarith
  refine ⟨N, (div_lt_iff₀ (by positivity : 0 < 4*a)).mpr (by linarith), fun ij => ?_⟩
  obtain ⟨h1,h2⟩ := opticalShellMode_radius hL N ij
  exact ⟨hlo.trans_le h1, h2.trans_lt (by change 6*a*N < 2*K; nlinarith)⟩

/-- A finite subsum of the actual variance grows at least linearly in
the shell radius, including the squared modulus of the entire contour. -/
theorem opticalRect_shell_variance {L h y K : ℝ} (hL : 0 < L) (hh : 0 < h) (hy : 0 < y)
    (hK : 28 * opticalSpacing L < K) :
    ∃ S : Finset OpticalMode, (∀ n ∈ S, K < ‖opticalTorusMode L n‖ ∧ ‖opticalTorusMode L n‖ < 2*K) ∧
      (1-exp (-(2*opticalSpacing L*y))) * h^2 / (16*(opticalSpacing L)^2) * K ≤
        ∑ n ∈ S, opticalRectModeVariance hL hh y n := by
  classical
  let a := opticalSpacing L
  have ha : 0 < a := by dsimp [a,opticalSpacing]; positivity
  have hk : 0 < K := by change 28*a < K at hK; linarith
  obtain ⟨N,hN,hs⟩ := opticalRect_shell_family hL hK
  let c := 1-exp (-(2*a*y))
  have hc : 0 < c := sub_pos.mpr (exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity)))
  let S := Finset.univ.image (opticalShellMode N)
  refine ⟨S, ?_, ?_⟩
  · intro n hn
    obtain ⟨ij,_,rfl⟩ := Finset.mem_image.mp hn
    exact hs ij
  have he (ij : Fin N × Fin N) : c*h^2/K ≤ opticalRectModeVariance hL hh y (opticalShellMode N ij) := by
    let k := ‖opticalTorusMode L (opticalShellMode N ij)‖
    have hs1 : K < k := (hs ij).1
    have hs2 : k < 2*K := (hs ij).2
    have hka : a ≤ k := by change 28*a < K at hK; linarith
    have hl := (opticalDirichletGreen_diag_lower ha hka hy).2
    change c/(2*k) ≤ opticalDirichletGreen k y y at hl
    unfold opticalRectModeVariance
    rw [show thinCurrentNormSq (opticalRectEdges hL hh) (opticalTorusMode L (opticalShellMode N ij)) =
      (2*h)^2 from opticalRect_odd_normSq _ _ _ _]
    calc
      c*h^2/K = c/(4*K)*(2*h)^2 := by field_simp; ring
      _ ≤ opticalDirichletGreen k y y*(2*h)^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact (div_le_div_of_nonneg_left hc.le (by linarith) (by linarith)).trans hl
  rw [Finset.sum_image (fun _ _ _ _ he => opticalShellMode_injective _ he)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N × Fin N))) (fun ij _ => he ij)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_mul] at hsum
  apply le_trans _ hsum
  have hN' := (sq_le_sq₀ (show 0 ≤ K/(4*a) by positivity) (Nat.cast_nonneg N)).mpr hN.le
  have hscale := mul_le_mul_of_nonneg_right hN' (show 0 ≤ c*h^2/K by positivity)
  change c*h^2/(16*a^2)*K ≤ _
  convert hscale using 1 <;> field_simp
  ring

theorem opticalRect_variance_diverges {L h y : ℝ} (hL : 0 < L) (hh : 0 < h) (hy : 0 < y) :
    ¬ Summable (opticalRectModeVariance hL hh y) := by
  intro hs
  let a := opticalSpacing L
  let c := (1-exp (-(2*a*y))) * h^2 / (16*a^2)
  have ha : 0 < a := by dsimp [a,opticalSpacing]; positivity
  have hc : 0 < c := by
    dsimp [c]
    have ht : 0 < 1-exp (-(2*a*y)) := sub_pos.mpr (exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity)))
    positivity
  let V := ∑' n, opticalRectModeVariance hL hh y n
  let K := max (28*a) (V/c) + 1
  have hK : 28*a < K := lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one
  obtain ⟨S,_,hb⟩ := opticalRect_shell_variance hL hh hy hK
  have hu : c*K ≤ V := hb.trans (hs.sum_le_tsum S (fun n _ => opticalRectModeVariance_nonneg hL hh hy.le n))
  have hV : V/c < K := lt_add_of_le_of_pos (le_max_right _ _) zero_lt_one
  have := (div_lt_iff₀ hc).mp hV
  linarith [mul_comm c K]

/-- The white-in-GT fluctuation tested with a unit-L² time smearing has
infinite nonnegative mode sum, including the torus volume normalization. -/
theorem opticalRect_white_time_variance {L h y : ℝ} (hL : 0 < L) (hh : 0 < h)
    (_hhL : h < L) (hy : 0 < y) (w : ℝ → ℝ) (hw : (∫ t, w t ^ 2) = 1) :
    (∑' n : OpticalMode, ENNReal.ofReal
      ((∫ t, w t^2 * opticalRectModeVariance hL hh y n) / L^3)) = ⊤ := by
  by_contra hfin
  have hs := ENNReal.summable_toReal hfin
  have hn : ∀ n, 0 ≤ opticalRectModeVariance hL hh y n := opticalRectModeVariance_nonneg hL hh hy.le
  have he (n : OpticalMode) :
      (ENNReal.ofReal ((∫ t, w t^2 * opticalRectModeVariance hL hh y n) / L^3)).toReal =
        opticalRectModeVariance hL hh y n / L^3 := by
    rw [integral_mul_const, hw, one_mul, ENNReal.toReal_ofReal (div_nonneg (hn _) (by positivity))]
  have hs' : Summable (fun n => opticalRectModeVariance hL hh y n / L^3) := by simpa only [he] using hs
  apply opticalRect_variance_diverges hL hh hy
  exact (hs'.mul_left (L^3)).congr fun n => by field_simp

end UV
