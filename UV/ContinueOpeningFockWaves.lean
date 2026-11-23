import UV.ExtendOpeningSpectral
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Gaussian Gram kernel and totality of the physical position-exponential
vacuum orbit in the oscillator number representation. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
namespace UV

def openingFockWave (t : ℝ) := openingCoherentVector ((t : ℂ)*Complex.I)

private theorem opening_wave_coord (t : ℝ) (n : ℕ) :
    openingFockWave t n = (Real.exp (-t^2/2) : ℂ)*((t:ℂ)*Complex.I)^n/(Real.sqrt (n.factorial:ℝ):ℂ) := by
  change openingCoherentCoefficient _ _ = _
  simp [openingCoherentCoefficient,Real.norm_eq_abs,sq_abs]

private theorem opening_wave_pair_term (s t : ℝ) (n : ℕ) :
    inner ℂ (openingFockWave s n) (openingFockWave t n) =
    (Real.exp (-s^2/2)*Real.exp (-t^2/2):ℝ)*((s*t:ℝ):ℂ)^n/(n.factorial:ℂ) := by
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hsq : ((Real.sqrt (n.factorial:ℝ):ℂ))^2 = (n.factorial:ℂ) := by exact_mod_cast Real.sq_sqrt hf.le
  rw [opening_wave_coord,opening_wave_coord]
  simp only [RCLike.inner_apply, map_div₀,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_mul]
  rw [div_mul_div_comm,←pow_two,hsq]
  congr 1
  calc _ = ((Real.exp (-s^2/2):ℂ)*(Real.exp (-t^2/2):ℂ))*(((t:ℂ)*Complex.I)^n*((s:ℂ)* -Complex.I)^n) := by ring
       _ = _ := by rw [←mul_pow]; congr 2; ring_nf; simp

theorem opening_fock_wave_gram (s t : ℝ) :
    inner ℂ (openingFockWave s) (openingFockWave t) = (Real.exp (-(s-t)^2/2):ℂ) := by
  rw [lp.inner_eq_tsum]
  simp_rw [opening_wave_pair_term,mul_div_assoc,tsum_mul_left]
  rw [←congrFun (NormedSpace.exp_eq_tsum_div (𝕂 := ℂ) (𝔸 := ℂ)) ((s*t:ℝ):ℂ),←Complex.exp_eq_exp_ℂ,←Complex.ofReal_exp,←Complex.ofReal_mul]
  congr 1
  rw [←Real.exp_add,←Real.exp_add]
  congr 1; ring

private theorem opening_power_unique (d : ℕ → ℂ) (B : ℝ) (hb : ∀ n, ‖d n‖ ≤ B)
    (h : ∀ t ∈ Ioc (0:ℝ) (1/2), (∑' k : ℕ, d k*(t:ℂ)^k) = 0) : ∀ n,d n = 0 := by
  let S := fun (n : ℕ) (t : ℝ) => ∑' k : ℕ, d (k+n)*(t:ℂ)^k
  have hsum : Summable (fun k : ℕ => B*((1/2:ℝ)^k)) := (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ)<1)).mul_left _
  have hbound (n k : ℕ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/2)) :
      ‖d (k+n)*(t:ℂ)^k‖ ≤ B*(1/2:ℝ)^k := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ht.1]
    exact mul_le_mul (hb _) (pow_le_pow_left₀ ht.1 ht.2 k) (pow_nonneg ht.1 _) ((norm_nonneg (d 0)).trans (hb 0))
  have hcont n : ContinuousOn (S n) (Icc 0 (1/2)) :=
    continuousOn_tsum (fun k => by fun_prop) hsum (hbound n)
  have atZero (n : ℕ) (hn : ∀ t ∈ Ioc (0:ℝ) (1/2), S n t=0) : d n=0 := by
    have hm : (0:ℝ) ∈ closure (Ioc 0 (1/2)) := by rw [closure_Ioc (by norm_num : (0:ℝ)≠1/2)]; constructor <;> norm_num
    haveI : NeBot (𝓝[Ioc (0:ℝ) (1/2)] 0) := mem_closure_iff_nhdsWithin_neBot.mp hm
    have h₁ := ((hcont n) 0 (show (0:ℝ)∈Icc 0 (1/2) by constructor <;> norm_num)).mono Ioc_subset_Icc_self
    have h₂ : Tendsto (S n) (𝓝[Ioc (0:ℝ) (1/2)] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hn t ht).symm)
    have hh : S n 0=0 := tendsto_nhds_unique h₁ h₂
    have hval : S n 0 = d n := by
      dsimp only [S]
      rw [tsum_eq_single 0 (fun k hk => by simp [hk])]
      simp
    exact hval.symm.trans hh
  have hSn (n : ℕ) : ∀ t ∈ Ioc (0:ℝ) (1/2), S n t=0 := by
    induction n with
    | zero => simpa [S] using h
    | succ n ih =>
      have hd := atZero n ih
      intro t ht
      have ha := hsum.of_norm_bounded (f := fun k => d (k+n)*(t:ℂ)^k) (fun k => hbound n k t ⟨ht.1.le,ht.2⟩)
      have hu := ih t ht
      rw [show S n t = _ from ha.tsum_eq_zero_add] at hu
      simp only [zero_add,pow_zero,mul_one,hd,zero_add] at hu
      have he : S (n+1) t * (t:ℂ) = 0 := by
        dsimp [S]
        rw [←tsum_mul_right]
        convert hu using 1
        apply tsum_congr; intro k
        rw [show k+1+n=k+(n+1) by omega,pow_succ]; ring
      exact (mul_eq_zero.mp he).resolve_right (Complex.ofReal_ne_zero.mpr ht.1.ne')
  exact fun n => atZero n (hSn n)

theorem opening_fock_wave_total :
    (Submodule.span ℂ (range openingFockWave)).topologicalClosure = ⊤ := by
  rw [←Submodule.orthogonal_orthogonal_eq_closure,Submodule.orthogonal_eq_top_iff]
  apply le_antisymm _ bot_le
  intro x hx
  let d := fun n : ℕ => (starRingEnd ℂ) (x n)*Complex.I^n/(Real.sqrt (n.factorial:ℝ):ℂ)
  have hs (n : ℕ) : 1 ≤ Real.sqrt (n.factorial:ℝ) := by
    exact (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).2 (by exact_mod_cast (Nat.factorial_pos n))
  have hb (n) : ‖d n‖ ≤ ‖x‖ := by
    simp only [d,norm_div,norm_mul,norm_pow,Complex.norm_conj,Complex.norm_I,one_pow,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_self (norm_nonneg _) (hs n)).trans (lp.norm_apply_le_norm (by norm_num) x n)
  have hd : ∀ n,d n=0 := by
    apply opening_power_unique d ‖x‖ hb
    intro t _
    have hxt : inner ℂ x (openingFockWave t) = 0 := inner_eq_zero_symm.mp (hx _ (Submodule.subset_span ⟨t,rfl⟩))
    rw [lp.inner_eq_tsum] at hxt
    have hterm (k : ℕ) : inner ℂ (x k) (openingFockWave t k) = (Real.exp (-t^2/2) : ℂ)*(d k*(t:ℂ)^k) := by
      rw [opening_wave_coord,RCLike.inner_apply]; dsimp only [d]; rw [mul_pow]; ring
    simp_rw [hterm,tsum_mul_left] at hxt
    exact (mul_eq_zero.mp hxt).resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  change x=0
  ext n
  have hh := hd n
  simpa [d,div_eq_zero_iff,mul_eq_zero,Complex.I_ne_zero,Real.sqrt_ne_zero'.mpr (show (0:ℝ)<n.factorial by exact_mod_cast Nat.factorial_pos n)] using hh

end UV
