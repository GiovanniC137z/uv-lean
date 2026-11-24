import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A one-dimensional finite-type sublevel estimate on the actual chart slice.
Repeated application of the mean-value theorem to disjoint pairs of separated
nodes gives the same exponent as the divided-difference proof. -/

noncomputable section
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace UV.SewnFlags

/-- A set larger than the union of `n` intervals of radius `δ` has
`n` distinct pairwise `δ`-separated points. No measurability is needed. -/
private theorem separated_points_of_volume {A : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (n : ℕ) (hA : ENNReal.ofReal ((n : ℝ) * (2 * δ)) < volume A) :
    ∃ s : Finset ℝ, s.card = n ∧ (↑s : Set ℝ) ⊆ A ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y| := by
  classical
  induction n with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ n ih =>
    have hmono : (n : ℝ) * (2 * δ) ≤ ((n + 1 : ℕ) : ℝ) * (2 * δ) := by
      push_cast; nlinarith
    obtain ⟨s, hs, hsub, hsep⟩ := ih ((ENNReal.ofReal_le_ofReal hmono).trans_lt hA)
    let B := ⋃ x ∈ s, Metric.ball x δ
    have hB : volume B ≤ ENNReal.ofReal ((n : ℝ) * (2 * δ)) := by
      apply (measure_biUnion_finset_le s (fun x : ℝ => Metric.ball x δ)).trans
      simp [Real.volume_ball, hs, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    have hnot : ¬ A ⊆ B := fun h => (not_lt_of_ge ((measure_mono h).trans hB))
      ((ENNReal.ofReal_le_ofReal hmono).trans_lt hA)
    obtain ⟨x, hxA, hxB⟩ := Set.not_subset.mp hnot
    have sep (y : ℝ) (hy : y ∈ s) : δ ≤ |x - y| := by
      by_contra! h
      exact hxB (Set.mem_iUnion₂.mpr ⟨y, hy, by simpa [Real.dist_eq] using h⟩)
    have hx : x ∉ s := by
      intro h; simpa using (hδ.not_ge (by simpa using sep x h))
    refine ⟨insert x s, by simp [hx, hs], ?_, ?_⟩
    · simpa using Set.insert_subset hxA hsub
    · intro u hu v hv huv
      rcases Finset.mem_insert.mp hu with he | hu₀
      · subst u
        exact sep v ((Finset.mem_insert.mp hv).resolve_left huv.symm)
      · rcases Finset.mem_insert.mp hv with he | hv₀
        · subst v; rw [abs_sub_comm]; exact sep u hu₀
        · exact hsep u hu₀ v hv₀ huv

/-- At `2^m` ordered, separated sublevel points the ordinary `m`th derivative
is small somewhere on the same open interval. -/
private theorem derivative_at_separated_nodes {a b δ : ℝ} (hδ : 0 < δ) (m : ℕ)
    (f : ℝ → ℝ) (hf : ∀ j, ∀ y ∈ Ioo a b, DifferentiableAt ℝ (iteratedDeriv j f) y)
    (r : ℝ) (hr : 0 ≤ r) (x : Fin (2 ^ m) → ℝ) (hx : ∀ i, x i ∈ Ioo a b)
    (hsep : ∀ i j, i < j → δ ≤ x j - x i) (hsmall : ∀ i, |f (x i)| ≤ r) :
    ∃ y ∈ Ioo a b, |iteratedDeriv m f y| ≤ (2 / δ)^m * r := by
  induction m generalizing f r with
  | zero =>
    exact ⟨x 0, hx _, by simpa using hsmall 0⟩
  | succ m ih =>
    let L (i : Fin (2^m)) : Fin (2^(m+1)) := ⟨2*i.val, by rw [pow_succ]; omega⟩
    let R (i : Fin (2^m)) : Fin (2^(m+1)) := ⟨2*i.val+1, by rw [pow_succ]; omega⟩
    have hpair (i) := hsep (L i) (R i) (show (L i).val < (R i).val by dsimp [L,R]; omega)
    have hdiff (z) (hz : z ∈ Ioo a b) : DifferentiableAt ℝ f z := by simpa using hf 0 z hz
    have hnodes (i) : ∃ y ∈ Ioo (x (L i)) (x (R i)), |deriv f y| ≤ 2 / δ * r := by
      have hgap := hpair i
      have hi : x (L i) < x (R i) := by linarith
      have hsubset : Icc (x (L i)) (x (R i)) ⊆ Ioo a b := fun z hz =>
        ⟨(hx _).1.trans_le hz.1, hz.2.trans_lt (hx _).2⟩
      obtain ⟨y,hy,hy'⟩ := exists_deriv_eq_slope f hi
        (fun z hz => (hdiff _ (hsubset hz)).continuousAt.continuousWithinAt)
        (fun z hz => (hdiff _ (hsubset (Ioo_subset_Icc_self hz))).differentiableWithinAt)
      refine ⟨y,hy,?_⟩
      rw [hy', abs_div, abs_of_pos (sub_pos.mpr hi)]
      calc
        _ ≤ (r + r) / (x (R i) - x (L i)) :=
          div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add (hsmall _) (hsmall _))) (by linarith)
        _ ≤ (r+r)/δ := div_le_div_of_nonneg_left (by positivity) hδ hgap
        _ = _ := by ring
    choose y hy hy' using hnodes
    obtain ⟨z,hz,hz'⟩ := ih (deriv f)
      (fun j t ht => by simpa only [← iteratedDeriv_succ'] using hf (j+1) t ht)
      (2/δ*r) (by positivity) y (fun i => ⟨(hx _).1.trans (hy i).1, (hy i).2.trans (hx _).2⟩)
      (by
        intro i j hij
        have hidx : R i < L j := by change 2*i.val+1 < 2*j.val; omega
        linarith [hsep _ _ hidx, (hy i).2, (hy j).1]) hy'
    exact ⟨z,hz, by simpa [iteratedDeriv_succ', pow_succ, mul_assoc] using hz'⟩

/-- A uniform nonzero `m`th derivative forces a power-law sublevel estimate,
including stationary points of all finite orders. -/
theorem finite_type_slice_volume {a b : ℝ} (m : ℕ) (hm : 0 < m)
    (f : ℝ → ℝ) (hf : ∀ j, ∀ y ∈ Ioo a b, DifferentiableAt ℝ (iteratedDeriv j f) y)
    {c : ℝ} (hc : 0 < c) (hder : ∀ y ∈ Ioo a b, c ≤ |iteratedDeriv m f y|)
    {r : ℝ} (hr : 0 < r) :
    volume {y ∈ Ioo a b | |f y| < r} ≤
      ENNReal.ofReal ((2^m : ℝ) * 8 * (r/c)^(1/(m:ℝ))) := by
  classical
  let u := (r/c)^(1/(m:ℝ))
  have hu : 0 < u := Real.rpow_pos_of_pos (div_pos hr hc) _
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hu_pow : u^m = r/c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hr hc).le, one_div_mul_cancel hm', Real.rpow_one]
  let δ := 4*u
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_contra! h
  have hA : ENNReal.ofReal (((2^m : ℕ) : ℝ) * (2*δ)) < volume {y ∈ Ioo a b | |f y| < r} := by
    convert h using 2
    push_cast; dsimp [δ,u]; ring
  obtain ⟨s,hcard,hsub,hsep⟩ := separated_points_of_volume hδ _ hA
  let x := s.orderEmbOfFin hcard
  have hx (i) := hsub (s.orderEmbOfFin_mem hcard i)
  have hxs (i j) (hij : i < j) : δ ≤ x j - x i := by
    have hji := x.strictMono hij
    change δ ≤ s.orderEmbOfFin hcard j - s.orderEmbOfFin hcard i
    rw [← abs_of_pos (sub_pos.mpr hji)]
    exact
      hsep _ (s.orderEmbOfFin_mem hcard j) _ (s.orderEmbOfFin_mem hcard i) hji.ne'
  obtain ⟨y,hy,hbound⟩ := derivative_at_separated_nodes hδ m f hf r hr.le x
    (fun i => (hx i).1) hxs (fun i => (hx i).2.le)
  have hbase : 2 / δ = (2 * u)⁻¹ := by dsimp [δ]; field_simp; ring
  have hcost : (2/δ)^m*r = c / (2:ℝ)^m := by
    rw [hbase, inv_pow, mul_pow, hu_pow]; field_simp
  have hpow : (1:ℝ) < 2^m := one_lt_pow₀ (by norm_num) hm.ne'
  have := hder y hy
  rw [hcost] at hbound
  exact (not_lt_of_ge (this.trans hbound)) (div_lt_self hc hpow)

end UV.SewnFlags
