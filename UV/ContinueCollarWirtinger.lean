import UV.ContinueCollarMesh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Sharp interval Dirichlet comparison by the positive cosine ground
state, avoiding any pre-existing spectral theorem for the Laplacian. -/

noncomputable section

open MeasureTheory Set Real
open scoped Interval

namespace UV.CollarEigenmode

theorem dirichlet_wirtinger {a b : ℝ} (hab : a < b) (u g : ℝ → ℝ)
    (hC : ContinuousOn u (Icc a b)) (hu : ∀ x ∈ Ioo a b,HasDerivAt u (g x) x)
    (ha : u a=0) (hb : u b=0) (hg : IntervalIntegrable g volume a b)
    (hg₂ : IntervalIntegrable (fun x => g x^2) volume a b) :
    (π/(b-a))^2*(∫ x in a..b,u x^2) ≤ ∫ x in a..b,g x^2 := by
  let K := π/(b-a)
  have hK : 0 < K := div_pos pi_pos (sub_pos.mpr hab)
  let S := {k : ℝ | k^2*(∫ x in a..b,u x^2) ≤ ∫ x in a..b,g x^2}
  have hS : IsClosed S := isClosed_le (by fun_prop) continuous_const
  have hsub : Ioo 0 K ⊆ S := by
    intro k hk
    have hk' : k*(b-a)<π := (lt_div_iff₀ (sub_pos.mpr hab)).mp hk.2
    let p (x : ℝ) := k*(x-(a+b)/2)
    let w (x : ℝ) := k*tan (p x)
    have hangle (x : ℝ) (hx : x ∈ Icc a b) : p x ∈ Ioo (-(π/2)) (π/2) := by
      dsimp [p]
      constructor
      · nlinarith only [hk',mul_nonneg hk.1.le (sub_nonneg.mpr hx.1)]
      · nlinarith only [hk',mul_nonneg hk.1.le (sub_nonneg.mpr hx.2)]
    have hw (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt w (k^2+w x^2) x := by
      have hp : HasDerivAt p k x := by simpa [p] using (((hasDerivAt_id x).sub_const ((a+b)/2)).const_mul k)
      have hcos := (cos_pos_of_mem_Ioo (hangle x hx)).ne'
      have htan := ((hasDerivAt_tan hcos).comp x hp).const_mul k
      have htrig := congrArg (fun z : ℝ => z⁻¹) (inv_one_add_tan_sq hcos)
      simp only [inv_inv] at htrig
      convert htan using 1
      simp only [w,one_div,← htrig]
      ring
    have hW : ContinuousOn w (Icc a b) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
    let v (x : ℝ) := g x*(2*u x*w x)+(k^2+w x^2)*u x^2
    have hv : IntervalIntegrable v volume a b := by
      rw [← uIcc_of_le hab.le] at hW hC
      exact (hg.mul_continuousOn ((continuousOn_const.mul hC).mul hW)).add (((continuousOn_const.add (hW.pow 2)).mul (hC.pow 2)).intervalIntegrable)
    have hD (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt (fun y => w y*u y^2) (v x) x := by
      convert (hw x (Ioo_subset_Icc_self hx)).mul ((hu x hx).pow 2) using 1
      dsimp [v]
      ring
    have hzero := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le (hW.mul (hC.pow 2)) hD hv
    simp [ha,hb] at hzero
    have hi := (hC.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
    have hnn : 0 ≤ ∫ x in a..b,(g x^2 + v x)-k^2*u x^2 := by
      apply intervalIntegral.integral_nonneg hab.le
      intro x _
      dsimp [v]
      nlinarith only [sq_nonneg (g x+w x*u x)]
    rw [intervalIntegral.integral_sub (hg₂.add hv) (hi.const_mul _),intervalIntegral.integral_add hg₂ hv,
      intervalIntegral.integral_const_mul,hzero,add_zero] at hnn
    exact sub_nonneg.mp hnn
  have hz := closure_minimal hsub hS
  rw [closure_Ioo hK.ne] at hz
  exact hz ⟨hK.le,le_rfl⟩

/-- The Dirichlet comparison for a trial space of dimension n+1, indexed
from zero. Both collar endpoints satisfy the Dirichlet trace. -/
theorem dirichlet_mesh_eigenvalue_lower (n : ℕ)
    (U : (Fin (n+1) → ℝ) →ₗ[ℝ] (ℝ → ℝ)) (g : (Fin (n+1) → ℝ) → ℝ → ℝ) (E : ℝ)
    (hC : ∀ c,ContinuousOn (U c) (Icc 0 1))
    (hu : ∀ c x,x ∈ Ioo 0 1 → HasDerivAt (U c) (g c x) x)
    (hl : ∀ c,U c 0=0) (hr : ∀ c,U c 1=0)
    (hg : ∀ c,IntervalIntegrable (g c) volume 0 1)
    (hg₂ : ∀ c,IntervalIntegrable (fun r => (g c r)^2) volume 0 1)
    (hnorm : ∀ c,c ≠ 0 → 0 < ∫ r in (0:ℝ)..1,(U c r)^2)
    (hform : ∀ c,(∫ r in (0:ℝ)..1,(g c r)^2) ≤ E*(∫ r in (0:ℝ)..1,(U c r)^2)) :
    π^2*((n:ℝ)+1)^2 ≤ E := by
  let d := fun i : ℕ => (i : ℝ)/((n:ℝ)+1)
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hd₀ : d 0 = 0 := by simp [d]
  have hd₁ : d (n+1) = 1 := by simp [d,hn.ne']
  have hd : StrictMono d := fun i j hij => div_lt_div_of_pos_right (by exact_mod_cast hij) hn
  let sampling : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi (fun i => (LinearMap.proj (d (i.val+1))).comp U)
  have hni : ¬ Function.Injective sampling := by
    intro h
    have hdim := LinearMap.finrank_le_finrank_of_injective h
    simp at hdim
  obtain ⟨v,w,he,hne⟩ := Function.not_injective_iff.mp hni
  let c := v-w
  have hc : c ≠ 0 := sub_ne_zero.mpr hne
  have hzero : sampling c=0 := by simp [c,he]
  have hsamp (i : ℕ) (hi : i ≤ n+1) : U c (d i)=0 := by
    cases i with
    | zero => simpa [hd₀] using hl c
    | succ i =>
      rcases (show i ≤ n by omega).eq_or_lt with rfl | hi'
      · simpa [hd₁] using hr c
      · exact congrFun hzero (⟨i,hi'⟩ : Fin n)
  have hS (i : ℕ) (hi : i<n+1) : Icc (d i) (d (i+1)) ⊆ Icc 0 1 :=
    Icc_subset_Icc (hd₀ ▸ hd.monotone (Nat.zero_le i)) (hd₁ ▸ hd.monotone (by omega))
  have hS' (i : ℕ) (hi : i<n+1) : [[d i,d (i+1)]] ⊆ [[(0:ℝ),1]] := by
    simpa only [uIcc_of_le (hd (Nat.lt_succ_self i)).le,uIcc_of_le zero_le_one] using hS i hi
  have hcell (i : ℕ) (hi : i<n+1) :
      (π^2*((n:ℝ)+1)^2)*(∫ r in d i..d (i+1),(U c r)^2) ≤ ∫ r in d i..d (i+1),(g c r)^2 := by
    have h := dirichlet_wirtinger (hd (Nat.lt_succ_self i)) (U c) (g c) ((hC c).mono (hS i hi))
      (fun x hx => hu c x ⟨lt_of_le_of_lt (hd₀ ▸ hd.monotone (Nat.zero_le i)) hx.1,
        lt_of_lt_of_le hx.2 (hd₁ ▸ hd.monotone (by omega))⟩) (hsamp i hi.le) (hsamp (i+1) hi)
      ((hg c).mono_set (hS' i hi)) ((hg₂ c).mono_set (hS' i hi))
    have hlen : d (i+1)-d i=((n:ℝ)+1)⁻¹ := by simp [d,add_div,one_div]
    rwa [hlen,div_inv_eq_mul,mul_pow] at h
  have hsum := Finset.sum_le_sum (s := Finset.range (n+1)) (fun i hi => hcell i (Finset.mem_range.mp hi))
  have hU := ((hC c).pow 2).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  rw [← Finset.mul_sum,intervalIntegral.sum_integral_adjacent_intervals (fun i hi => hU.mono_set (hS' i hi)),
    intervalIntegral.sum_integral_adjacent_intervals (fun i hi => (hg₂ c).mono_set (hS' i hi)),hd₀,hd₁] at hsum
  exact le_of_mul_le_mul_right (hsum.trans (hform c)) (hnorm c hc)

end UV.CollarEigenmode
