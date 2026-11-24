import UV.ContinueOrderedHopWinding
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.SpecificLimits.Normed

/-! Mean-zero reciprocal modes of a rectangular spatial three-torus. The
integer cube height counts lattice points; the propagators use the Euclidean
norm of the actual momentum. -/

noncomputable section
open Set MeasureTheory Real
open scoped ENNReal
namespace UV.SectorPlane

/-- For periods `2π/δⱼ`, these are the three spatial momenta. The cubic box of
the manuscript has all three spacings equal to `R⁻¹`. -/
def orderedTorusMomentum (δ : Fin 3 → ℝ) (k : OrderedHopWinding) : Spatial :=
  WithLp.toLp 2 (fun i => δ i*(k i:ℝ))

private def cube (n : ℕ) : Finset OrderedHopWinding :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(n:ℤ)) (n:ℤ)

private def height (k : OrderedHopWinding) := Finset.univ.sup (fun i => (k i).natAbs)

private theorem height_le {n : ℕ} {k : OrderedHopWinding} : height k ≤ n ↔ k ∈ cube n := by
  rw [height, Finset.sup_le_iff, cube, Fintype.mem_piFinset]
  simp only [Finset.mem_univ,true_implies, Finset.mem_Icc]
  exact forall_congr' fun _ => by omega

private theorem cube_card (n : ℕ) : (cube n).card = (2*n+1)^3 := by
  have h : (Finset.Icc (-(n:ℤ)) (n:ℤ)).card = 2*n+1 := by rw [Int.card_Icc]; omega
  simp [cube,Fintype.card_piFinset,h]

private def shell (n : ℕ) := cube (n+1) \ cube n

private theorem mem_shell (n : ℕ) (k : OrderedHopWinding) : k ∈ shell n ↔ height k = n+1 := by
  rw [shell,Finset.mem_sdiff,←height_le,←height_le]; omega

private theorem shell_card (n : ℕ) : ((shell n).card : ℝ) ≤ 26*((n:ℝ)+1)^2 := by
  have hs : cube n ⊆ cube (n+1) := fun _ h => height_le.mp ((height_le.mpr h).trans (Nat.le_succ _))
  have h := Finset.card_sdiff_add_card_eq_card hs
  change (shell n).card+(cube n).card = (cube (n+1)).card at h
  rw [cube_card,cube_card] at h
  have h' := congrArg (fun k : ℕ => (k:ℝ)) h
  push_cast at h'
  nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n:ℝ)]

private theorem height_pos {k : OrderedHopWinding} (hk : k ≠ 0) : 0 < height k := by
  by_contra! h
  apply hk
  funext i
  have h' := (Finset.sup_le_iff.mp h) i (Finset.mem_univ i)
  change k i = 0
  change (k i).natAbs ≤ 0 at h'
  omega

theorem ordered_torus_height_gap {δ : Fin 3 → ℝ} {d : ℝ} (hd : 0 < d) (hδ : ∀ i, d ≤ δ i)
    (k : OrderedHopWinding) : d*(height k : ℝ) ≤ ‖orderedTorusMomentum δ k‖ := by
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin 3)))
    (f := fun i => (k i).natAbs) Finset.univ_nonempty
  have h := PiLp.norm_apply_le (orderedTorusMomentum δ k) j
  change |δ j*(k j:ℝ)| ≤ _ at h
  rw [abs_mul,abs_of_pos (hd.trans_le (hδ _))] at h
  unfold height; rw [hj,←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  exact (mul_le_mul_of_nonneg_right (hδ _) (abs_nonneg _)).trans h

theorem ordered_torus_gap {δ : Fin 3 → ℝ} {d : ℝ} (hd : 0 < d) (hδ : ∀ i, d ≤ δ i)
    {k : OrderedHopWinding} (hk : k ≠ 0) : d ≤ ‖orderedTorusMomentum δ k‖ :=
  (le_mul_of_one_le_right hd.le (by exact_mod_cast height_pos hk)).trans (ordered_torus_height_gap hd hδ k)

private theorem shell_sum_le (f : OrderedHopWinding → ℝ≥0∞) (hf : f 0 = 0) (B : ℕ → ℝ≥0∞)
    (h : ∀ n k, k ∈ shell n → f k ≤ B n) :
    ∑' k, f k ≤ ∑' n : ℕ, ENNReal.ofReal (26*((n:ℝ)+1)^2) * B n := by
  classical
  calc
    _ ≤ ∑' k, ∑' n : ℕ, if k ∈ shell n then B n else 0 := by
      apply ENNReal.tsum_le_tsum; intro k
      by_cases hz : k = 0
      · simp [hz,hf]
      · have hpos := height_pos hz
        let n := height k - 1
        have hk : k ∈ shell n := (mem_shell _ _).mpr (by dsimp [n]; omega)
        apply (h n k hk).trans
        simpa only [if_pos hk] using (ENNReal.le_tsum n (f := fun j => if k ∈ shell j then B j else 0))
    _ = ∑' n : ℕ, ∑' k, if k ∈ shell n then B n else 0 := ENNReal.tsum_comm
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum; intro n
      rw [tsum_eq_sum (s := shell n) (fun k hk => if_neg hk),Finset.sum_congr rfl
        (fun k hk => if_pos hk),Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_right'
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (shell_card n)

private theorem geometric_shell_powers {β : ℝ} (hβ : 0 < β) :
    (∑' n : ℕ, ENNReal.ofReal (exp (-β*((n:ℝ)+1)))) ≤ ENNReal.ofReal β⁻¹ ∧
    (∑' n : ℕ, ENNReal.ofReal (((n:ℝ)+1)*exp (-β*((n:ℝ)+1)))) ≤ ENNReal.ofReal (exp β / β^2) := by
  let z := exp (-β)
  have hz : 0 < z := exp_pos _
  have hz₁ : z < 1 := exp_lt_one_iff.mpr (by linarith)
  have hn : ‖z‖ < 1 := by simpa [Real.norm_of_nonneg hz.le] using hz₁
  have hgeom := hasSum_geometric_of_norm_lt_one hn
  have hgeom' := hasSum_coe_mul_geometric_of_norm_lt_one hn
  have he (n : ℕ) : exp (-β*((n:ℝ)+1)) = z*z^n := by
    rw [mul_add,mul_one,exp_add,mul_comm (-β) (n:ℝ),exp_nat_mul]; exact mul_comm _ _
  have hz' : z = (exp β)⁻¹ := exp_neg _
  have hβ' := add_one_le_exp β
  have hd : 0 < exp β-1 := by linarith
  have h₁ : z*(1-z)⁻¹ = (exp β-1)⁻¹ := by rw [hz']; field_simp
  have h₂ : z*(z/(1-z)^2+(1-z)⁻¹) = exp β / (exp β-1)^2 := by rw [hz']; field_simp; ring
  constructor
  · simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hz.le (pow_nonneg hz.le n))
        (hgeom.mul_left z).summable,(hgeom.mul_left z).tsum_eq,h₁]
    exact ENNReal.ofReal_le_ofReal (inv_anti₀ hβ (by linarith))
  · have hx (n : ℕ) : ((n:ℝ)+1)*exp (-β*((n:ℝ)+1)) = z*((n:ℝ)*z^n+z^n) := by rw [he]; ring
    simp_rw [hx]
    have hsum := (hgeom'.add hgeom).mul_left z
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n : ℕ => show 0 ≤ z*((n:ℝ)*z^n+z^n) by positivity)
        hsum.summable,hsum.tsum_eq,h₂]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (exp_pos _).le (by positivity)
      (pow_le_pow_left₀ hβ.le (by linarith) 2))

/-- Spatial sums after integrating a transverse or an instantaneous line in
its carrier frequency. The constants depend only on a lower reciprocal
spacing; every nonzero lattice point is included. -/
theorem ordered_torus_spatial_chord_budgets {δ : Fin 3 → ℝ} {d r : ℝ} (hd : 0 < d)
    (hδ : ∀ i, d ≤ δ i) (hr : 0 < r) :
    let β := 2*r*d
    (∑' k : OrderedHopWinding, if k = 0 then 0 else
      ENNReal.ofReal (exp (-(2*r*‖orderedTorusMomentum δ k‖))/‖orderedTorusMomentum δ k‖)) ≤
        ENNReal.ofReal (26/d) * ENNReal.ofReal (exp β / β^2) ∧
    (∑' k : OrderedHopWinding, if k = 0 then 0 else
      ENNReal.ofReal (exp (-(2*r*‖orderedTorusMomentum δ k‖))/‖orderedTorusMomentum δ k‖^2)) ≤
        ENNReal.ofReal (26/d^2) * ENNReal.ofReal β⁻¹ := by
  intro β
  have hβ : 0 < β := by dsimp [β]; positivity
  have hb (n : ℕ) (k : OrderedHopWinding) (hk : k ∈ shell n) :
      d*((n:ℝ)+1) ≤ ‖orderedTorusMomentum δ k‖ := by
    simpa only [(mem_shell _ _).mp hk, Nat.cast_add_one] using ordered_torus_height_gap hd hδ k
  have hsum (p : ℕ) : (∑' k : OrderedHopWinding, if k = 0 then 0 else
      ENNReal.ofReal (exp (-(2*r*‖orderedTorusMomentum δ k‖))/‖orderedTorusMomentum δ k‖^p)) ≤
      ∑' n : ℕ, ENNReal.ofReal (26*((n:ℝ)+1)^2) *
        ENNReal.ofReal (exp (-β*((n:ℝ)+1)) / (d*((n:ℝ)+1))^p) := by
    apply shell_sum_le _ (by simp)
    intro n k hk
    split_ifs
    · exact zero_le _
    · apply ENNReal.ofReal_le_ofReal
      apply div_le_div₀ (exp_pos _).le _ (by positivity) (pow_le_pow_left₀ (by positivity) (hb n k hk) p)
      apply exp_le_exp.mpr
      dsimp [β]; nlinarith [mul_le_mul_of_nonneg_left (hb n k hk) (by positivity : 0 ≤ 2*r)]
  obtain ⟨hs₀,hs₁⟩ := geometric_shell_powers hβ
  constructor
  · have h := hsum 1
    simp only [pow_one] at h
    apply h.trans
    calc
      _ = ENNReal.ofReal (26/d) * ∑' n : ℕ, ENNReal.ofReal (((n:ℝ)+1)*exp (-β*((n:ℝ)+1))) := by
        rw [← ENNReal.tsum_mul_left]; apply tsum_congr; intro n
        rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
      _ ≤ _ := mul_le_mul_left' hs₁ _
  · have h := hsum 2
    apply h.trans
    calc
      _ = ENNReal.ofReal (26/d^2) * ∑' n : ℕ, ENNReal.ofReal (exp (-β*((n:ℝ)+1))) := by
        rw [← ENNReal.tsum_mul_left]; apply tsum_congr; intro n
        rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
      _ ≤ _ := mul_le_mul_left' hs₀ _

end UV.SectorPlane
