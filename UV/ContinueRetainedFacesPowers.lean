import UV.ContinueRetainedFacesOrdered

/-! Convert the retained determinant comparison into the exact
prefix exponents, for any nonnegative real momentum weight. -/

noncomputable section

open Finset
open scoped BigOperators ENNReal

namespace UV

/-- Pointwise product density in the positive width coordinates. -/
def retainedWidthDensity {n : ℕ} (β t : Fin n → ℝ) : ℝ :=
  ∏ i, t i ^ (β i - 1)

private theorem retainedBasisProduct_eq {n : ℕ} (B : Finset (Fin n)) (t : Fin n → ℝ) :
    (∏ i, t i ^ retainedBasisExponent B i) = ∏ i ∈ B, t i := by
  have hi (i : Fin n) : t i ^ retainedBasisExponent B i = if i ∈ B then t i else 1 := by
    by_cases hb : i ∈ B <;> simp [retainedBasisExponent, hb]
  simp_rw [hi]
  rw [← Finset.prod_filter]
  simp

theorem retainedOrderedDensity_eq_basisRatio {n : ℕ} (β : Fin n → ℝ) (h : ℝ)
    (B D : Finset (Fin n)) (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) :
    directionalOrderedDensity (retainedOrderedExponent β h B D) t =
      ENNReal.ofReal (retainedWidthDensity β t / (∏ i ∈ B, t i) ^ 2 *
        ((∏ i ∈ D, t i) / (∏ i ∈ B, t i)) ^ h) := by
  unfold directionalOrderedDensity
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (ht i).le _)]
  congr 1
  have he (i : Fin n) : t i ^ (retainedOrderedExponent β h B D i - 1) =
    t i ^ (β i - 1) / (t i ^ retainedBasisExponent B i) ^ 2 *
      (t i ^ retainedBasisExponent D i / t i ^ retainedBasisExponent B i) ^ h := by
    rw [← Real.rpow_two, ← Real.rpow_mul (ht i).le, ← Real.rpow_sub (ht i),
      ← Real.rpow_sub (ht i), ← Real.rpow_mul (ht i).le, ← Real.rpow_add (ht i)]
    congr 1
    unfold retainedOrderedExponent
    ring
  simp_rw [he, Finset.prod_mul_distrib, Finset.prod_div_distrib]
  rw [Real.finset_prod_rpow _ _ (fun i _ => (div_pos (Real.rpow_pos_of_pos (ht i) _)
    (Real.rpow_pos_of_pos (ht i) _)).le) h, Finset.prod_div_distrib]
  rw [Finset.prod_pow, retainedBasisProduct_eq, retainedBasisProduct_eq]
  rfl

/-- Real powers of a finite sum of positive contributions are uniformly
comparable to a sum of the individual powers, including when the
exponent is zero. -/
theorem retainedSum_rpow_comparison {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) {h : ℝ} (hh : 0 ≤ h) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, x i ^ h) ≤ (Fintype.card ι : ℝ) * (∑ i, x i) ^ h ∧
      (∑ i, x i) ^ h ≤ (Fintype.card ι : ℝ) ^ h * (∑ i, x i ^ h) := by
  classical
  have hxsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  constructor
  · calc
      _ ≤ ∑ _ : ι, (∑ i, x i) ^ h := Finset.sum_le_sum fun i _ =>
        Real.rpow_le_rpow (hx i) (Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)) hh
      _ = _ := by simp
  · obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
    have hsum : (∑ i, x i) ≤ (Fintype.card ι : ℝ) * x i := by
      calc
        _ ≤ ∑ _ : ι, x i := Finset.sum_le_sum fun j hj => hi j hj
        _ = _ := by simp
    calc
      _ ≤ ((Fintype.card ι : ℝ) * x i) ^ h := Real.rpow_le_rpow hxsum hsum hh
      _ = (Fintype.card ι : ℝ) ^ h * x i ^ h := Real.mul_rpow (by positivity) (hx i)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hx j) h) (Finset.mem_univ i))
        (Real.rpow_nonneg (by positivity) _)

/-- A width-independent comparison for the negative determinant power
and the positive power of its cofactor ratio sum. -/
theorem retainedMoment_comparison {ι : Type*} [Fintype ι]
    (X Y : Option ι → ℝ) {lo hi h w : ℝ} (hlo : 0 < lo) (hhi : 0 < hi)
    (hh : 0 ≤ h) (hw : 0 ≤ w) (hy : ∀ i, 0 < Y i)
    (bounds : ∀ i, lo * Y i ≤ X i ∧ X i ≤ hi * Y i) :
    let G := ∑ i, w / Y none ^ 2 * (Y i / Y none) ^ h
    let F := w / X none ^ 2 * (∑ i, X i / X none) ^ h
    ((hi ^ 2)⁻¹ * (lo / hi) ^ h / (Fintype.card (Option ι) : ℝ)) * G ≤ F ∧
      F ≤ ((lo ^ 2)⁻¹ * (hi / lo) ^ h * (Fintype.card (Option ι) : ℝ) ^ h) * G := by
  dsimp only
  let a := fun i => X i / X none
  let b := fun i => Y i / Y none
  let sx := ∑ i, a i
  let sy := ∑ i, b i
  let ry := ∑ i, b i ^ h
  let c : ℝ := Fintype.card (Option ι)
  have hc : 0 < c := by
    unfold c
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨none⟩
  have hX (i : Option ι) : 0 < X i := (mul_pos hlo (hy i)).trans_le (bounds i).1
  have hA (i : Option ι) : 0 < a i := div_pos (hX i) (hX _)
  have hB (i : Option ι) : 0 < b i := div_pos (hy i) (hy _)
  have hb0 : 0 ≤ sy := Finset.sum_nonneg fun i _ => (hB i).le
  have hs0 : 0 ≤ sx := Finset.sum_nonneg fun i _ => (hA i).le
  have hr0 : 0 ≤ ry := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hB i).le _
  have hratio (i : Option ι) : (lo / hi) * b i ≤ a i ∧ a i ≤ (hi / lo) * b i := by
    unfold a b
    constructor
    · have h := div_le_div₀ (hX i).le (bounds i).1
        (hX none) (bounds none).2
      convert h using 1
      exact div_mul_div_comm lo hi (Y i) (Y none)
    · have h := div_le_div₀ (mul_nonneg hhi.le (hy i).le) (bounds i).2 (mul_pos hlo (hy none)) (bounds none).1
      convert h using 1
      exact div_mul_div_comm hi lo (Y i) (Y none)
  have hslo : lo / hi * sy ≤ sx := by
    unfold sx sy
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hratio i).1
  have hshi : sx ≤ hi / lo * sy := by
    unfold sx sy
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hratio i).2
  have hrlo : (lo / hi) ^ h * (ry / c) ≤ sx ^ h := by
    have hpow := Real.rpow_le_rpow (mul_nonneg (div_nonneg hlo.le hhi.le) hb0) hslo hh
    rw [Real.mul_rpow (div_nonneg hlo.le hhi.le) hb0] at hpow
    have hsum : ry / c ≤ sy ^ h :=
      (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using
        (retainedSum_rpow_comparison b hh (fun i => (hB i).le)).1)
    exact (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (div_nonneg hlo.le hhi.le) _)).trans hpow
  have hrhi : sx ^ h ≤ (hi / lo) ^ h * (c ^ h * ry) := by
    have hpow := Real.rpow_le_rpow hs0 hshi hh
    rw [Real.mul_rpow (div_nonneg hhi.le hlo.le) hb0] at hpow
    exact hpow.trans (mul_le_mul_of_nonneg_left
      (retainedSum_rpow_comparison b hh (fun i => (hB i).le)).2
      (Real.rpow_nonneg (div_nonneg hhi.le hlo.le) _))
  have hdenlo : (hi ^ 2)⁻¹ * (w / Y none ^ 2) ≤ w / X none ^ 2 := by
    have hp : X none ^ 2 ≤ (hi * Y none) ^ 2 := by
      exact pow_le_pow_left₀ (hX _).le (bounds none).2 2
    calc
      _ = w / (hi * Y none) ^ 2 := by rw [mul_pow]; ring
      _ ≤ _ := div_le_div_of_nonneg_left hw (pow_pos (hX _) _) hp
  have hdenhi : w / X none ^ 2 ≤ (lo ^ 2)⁻¹ * (w / Y none ^ 2) := by
    have hp : (lo * Y none) ^ 2 ≤ X none ^ 2 := by
      exact pow_le_pow_left₀ (mul_pos hlo (hy _)).le (bounds none).1 2
    calc
      _ ≤ w / (lo * Y none) ^ 2 := div_le_div_of_nonneg_left hw (pow_pos (mul_pos hlo (hy _)) _) hp
      _ = _ := by rw [mul_pow]; ring
  rw [← Finset.mul_sum]
  change (hi ^ 2)⁻¹ * (lo / hi) ^ h / c * (w / Y none ^ 2 * ry) ≤
      w / X none ^ 2 * sx ^ h ∧
    w / X none ^ 2 * sx ^ h ≤ (lo ^ 2)⁻¹ * (hi / lo) ^ h * c ^ h * (w / Y none ^ 2 * ry)
  constructor
  · calc
      _ = ((hi ^ 2)⁻¹ * (w / Y none ^ 2)) * ((lo / hi) ^ h * (ry / c)) := by ring
      _ ≤ _ := mul_le_mul hdenlo hrlo (by positivity) (div_nonneg hw (sq_nonneg _))
  · calc
      _ ≤ ((lo ^ 2)⁻¹ * (w / Y none ^ 2)) * ((hi / lo) ^ h * (c ^ h * ry)) :=
        mul_le_mul hdenhi hrhi (Real.rpow_nonneg hs0 _) (by positivity)
      _ = _ := by ring

end UV
