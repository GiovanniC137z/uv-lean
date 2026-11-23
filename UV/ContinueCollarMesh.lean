import UV.ContinueCollarEigenTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! A one-dimensional mesh gives quadratic eigenvalue growth directly from
the Dirichlet form on finite-dimensional trial spaces. -/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace UV.CollarEigenmode

private theorem integral_cauchy {a x : ℝ} (hx : a ≤ x) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a x)
    (hg₂ : IntervalIntegrable (fun y => g y ^ 2) volume a x) :
    (∫ y in a..x,g y)^2 ≤ (x-a)*(∫ y in a..x,g y^2) := by
  rcases hx.eq_or_lt with rfl | hax
  · simp
  let m := ∫ y in a..x,g y
  let l := x-a
  have hl : 0 < l := sub_pos.mpr hax
  have hp : 0 ≤ ∫ y in a..x, l^2*g y^2-2*l*m*g y+m^2 := by
    apply intervalIntegral.integral_nonneg hax.le
    intro y _
    nlinarith only [sq_nonneg (l*g y-m)]
  rw [intervalIntegral.integral_add ((hg₂.const_mul _).sub (hg.const_mul _))
      intervalIntegrable_const,intervalIntegral.integral_sub (hg₂.const_mul _) (hg.const_mul _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const,smul_eq_mul] at hp
  change m^2 ≤ l*(∫ y in a..x,g y^2)
  apply le_of_mul_le_mul_left _ hl
  change 0 ≤ l^2*(∫ y in a..x,g y^2)-2*l*m*m+l*m^2 at hp
  nlinarith only [hp]

theorem cell_poincare {a b : ℝ} (hab : a ≤ b) (u g : ℝ → ℝ)
    (hu₂ : IntervalIntegrable (fun y => u y^2) volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hg₂ : IntervalIntegrable (fun y => g y^2) volume a b)
    (hprim : ∀ x ∈ Icc a b,u x = ∫ y in a..x,g y) :
    (∫ y in a..b,u y^2) ≤ (b-a)^2*(∫ y in a..b,g y^2) := by
  let K := ∫ y in a..b,g y^2
  have hK : 0 ≤ K := intervalIntegral.integral_nonneg hab fun y _ => sq_nonneg (g y)
  calc
    _ ≤ ∫ _ in a..b,(b-a)*K := by
      apply intervalIntegral.integral_mono_on hab hu₂ intervalIntegrable_const
      intro x hx
      have hs : [[a,x]] ⊆ [[a,b]] := by simpa [uIcc_of_le hx.1,uIcc_of_le hab] using (Icc_subset_Icc_right (a:=a) hx.2)
      rw [hprim x hx]
      apply (integral_cauchy hx.1 g (hg.mono_set hs) (hg₂.mono_set hs)).trans
      have hI : (∫ y in a..x,g y^2) ≤ K := intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2 (Filter.Eventually.of_forall fun _ => sq_nonneg _) hg₂
      exact (mul_le_mul_of_nonneg_left hI (sub_nonneg.mpr hx.1)).trans (mul_le_mul_of_nonneg_right (sub_le_sub_right hx.2 a) hK)
    _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]; ring

/-- Any real trial space of dimension (n+1) with a Rayleigh upper bound
has upper energy at least (n²). Absolute continuity is expressed by its
integral-of-the-derivative identity, so singular endpoint derivatives are permitted. -/
theorem mesh_eigenvalue_lower (n : ℕ) (hn : 0 < n)
    (U : (Fin (n+1) → ℝ) →ₗ[ℝ] (ℝ → ℝ)) (g : (Fin (n+1) → ℝ) → ℝ → ℝ) (E : ℝ)
    (hu : ∀ c,IntervalIntegrable (fun r => (U c r)^2) volume 0 1)
    (hg : ∀ c,IntervalIntegrable (g c) volume 0 1)
    (hg₂ : ∀ c,IntervalIntegrable (fun r => (g c r)^2) volume 0 1)
    (hprim : ∀ c a x,0 ≤ a → a ≤ x → x ≤ 1 → U c x-U c a = ∫ r in a..x,g c r)
    (hnorm : ∀ c,c ≠ 0 → 0 < ∫ r in (0:ℝ)..1,(U c r)^2)
    (hform : ∀ c,(∫ r in (0:ℝ)..1,(g c r)^2) ≤ E*(∫ r in (0:ℝ)..1,(U c r)^2)) :
    (n:ℝ)^2 ≤ E := by
  let d := fun i : ℕ => (i : ℝ)/n
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hd₀ : d 0 = 0 := by simp [d]
  have hd₁ : d n = 1 := div_self hn'.ne'
  have hd : Monotone d := fun i j hij => div_le_div_of_nonneg_right (by exact_mod_cast hij) hn'.le
  let evalMesh : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi (fun i => (LinearMap.proj (d i.val)).comp U)
  have hni : ¬ Function.Injective evalMesh := by
    intro h
    have hdim := LinearMap.finrank_le_finrank_of_injective h
    simp at hdim
  obtain ⟨v,w,he,hne⟩ := Function.not_injective_iff.mp hni
  let c := v-w
  have hc : c ≠ 0 := sub_ne_zero.mpr hne
  have hzero : evalMesh c=0 := by simp [c,he]
  have hS (i : ℕ) (hi : i<n) : [[d i,d (i+1)]] ⊆ [[(0:ℝ),1]] := by
    rw [uIcc_of_le (hd (Nat.le_succ i)),uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (hd₀ ▸ hd (Nat.zero_le i)) (hd₁ ▸ hd (by omega))
  have hcell (i : ℕ) (hi : i<n) :
      (∫ r in d i..d (i+1),(U c r)^2) ≤ ((n:ℝ)⁻¹)^2*(∫ r in d i..d (i+1),(g c r)^2) := by
    have hzi : U c (d i)=0 := congrFun hzero (⟨i,hi⟩ : Fin n)
    have hz := cell_poincare (hd (Nat.le_succ i)) (U c) (g c)
      ((hu c).mono_set (hS i hi)) ((hg c).mono_set (hS i hi)) ((hg₂ c).mono_set (hS i hi)) (fun x hx => by
        have h := hprim c (d i) x (hd₀ ▸ hd (Nat.zero_le i)) hx.1 (hx.2.trans (hd₁ ▸ hd (by omega)))
        simpa only [hzi,sub_zero] using h)
    have hlen : d (i+1)-d i=(n:ℝ)⁻¹ := by simp [d,add_div,one_div]
    rwa [hlen] at hz
  have hS' := Finset.sum_le_sum (s := Finset.range n) (fun i hi => hcell i (Finset.mem_range.mp hi))
  rw [← Finset.mul_sum,intervalIntegral.sum_integral_adjacent_intervals (fun i hi => (hu c).mono_set (hS i hi)),
    intervalIntegral.sum_integral_adjacent_intervals (fun i hi => (hg₂ c).mono_set (hS i hi)),hd₀,hd₁] at hS'
  have hE := hS'.trans (mul_le_mul_of_nonneg_left (hform c) (sq_nonneg _))
  rw [← mul_assoc] at hE
  have hfactor : 1 ≤ ((n:ℝ)⁻¹)^2*E := (le_of_mul_le_mul_right (by simpa only [one_mul] using hE) (hnorm c hc))
  rw [inv_pow,← div_eq_inv_mul] at hfactor
  exact (le_div_iff₀ (sq_pos_of_pos hn')).mp hfactor |>.trans_eq' (one_mul _).symm

end UV.CollarEigenmode
