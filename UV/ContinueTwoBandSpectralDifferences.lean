import UV.ContinueTwoBandSpectralKernel

/-! Complete temporal marks on the two oriented onsite slots, in the
positive-exponential Fourier convention of the joint hopping estimate. The
signed real mass is (+m) or (-m) on the two slots of the selected plane. -/

noncomputable section
open MeasureTheory Complex Filter
open scoped Topology

namespace UV.SectorPlane

/-- Onsite factor for the `exp(i s u)` Fourier transform. -/
def hoppingInterval (a s : ℝ) : ℂ := ((a:ℂ)-I*s)⁻¹

/-- A normalized translation difference, continued at zero transfer by its real
frequency derivative divided by `i`. -/
def hoppingDifference (ν : ℝ) (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  if ν=0 then deriv f s/I else (f (s+ν)-f s)/(I*ν)

private theorem hopping_denom_ne {a : ℝ} (ha : a ≠ 0) (s : ℝ) : (a:ℂ)-I*s ≠ 0 := by
  intro h
  apply ha
  simpa [mul_re] using congrArg Complex.re h

theorem hopping_interval_derivative {a : ℝ} (ha : a ≠ 0) (s : ℝ) :
    HasDerivAt (hoppingInterval a) (I*(hoppingInterval a s)^2) s := by
  have h := (((hasDerivAt_id (s:ℂ)).const_mul I).const_sub (a:ℂ)).fun_inv (hopping_denom_ne ha s)
  convert h.comp_ofReal using 1
  simp [hoppingInterval,div_eq_mul_inv,inv_pow]

theorem hopping_interval_shift_derivative {a : ℝ} (ha : a ≠ 0) (b s : ℝ) :
    HasDerivAt (fun x => hoppingInterval a (x+b)) (I*(hoppingInterval a (s+b))^2) s := by
  exact (hopping_interval_derivative ha (s+b)).comp_add_const s b

/-- A single complete insertion yields both neighboring resolvents, even at zero transfer. -/
theorem hopping_single_difference {a : ℝ} (ha : a ≠ 0) (ν b s : ℝ) :
    hoppingDifference ν (fun x => hoppingInterval a (x+b)) s =
      hoppingInterval a (s+b) * hoppingInterval a (s+b+ν) := by
  by_cases hν : ν=0
  · simp [hoppingDifference,hν,(hopping_interval_shift_derivative ha b s).deriv,pow_two]
  · rw [hoppingDifference,if_neg hν,show s+ν+b=s+b+ν by ring]
    let d := (a:ℂ)-I*(s+b:ℝ)
    let e := (a:ℂ)-I*(s+b+ν:ℝ)
    have hd : d ≠ 0 := hopping_denom_ne ha _
    have he : e ≠ 0 := hopping_denom_ne ha _
    have hν' : (ν:ℂ) ≠ 0 := by exact_mod_cast hν
    have hdif : d-e = I*ν := by dsimp [d,e]; push_cast; ring
    change (e⁻¹-d⁻¹)/(I*ν) = d⁻¹*e⁻¹
    field_simp
    linear_combination hdif

theorem hopping_difference_tendsto {f : ℝ → ℂ} {s : ℝ} (hf : DifferentiableAt ℝ f s) :
    Tendsto (fun ν : ℝ => (f (s+ν)-f s)/(I*ν)) (𝓝[≠] 0) (𝓝 (hoppingDifference 0 f s)) := by
  have h := (hasDerivAt_iff_tendsto_slope_zero.mp hf.hasDerivAt)
  have he (ν : ℝ) : (f (s+ν)-f s)/(I*ν) = ((ν⁻¹:ℝ) • (f (s+ν)-f s))/I := by
    simp only [Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  simp_rw [he]
  simpa [hoppingDifference] using h.div_const I

/-- Both orderings on one interval are retained. Opposite nonzero transfers
produce the centered difference with the signed denominators of the manuscript. -/
theorem hopping_coulomb_pair (f : ℝ → ℂ) {ν : ℝ} (hν : ν ≠ 0) (s : ℝ) :
    hoppingDifference (-ν) (hoppingDifference ν f) s =
      (2*f s-f (s+ν)-f (s-ν))/(ν:ℂ)^2 := by
  simp only [hoppingDifference,if_neg hν,if_neg (neg_ne_zero.mpr hν),
    Complex.ofReal_neg,←sub_eq_add_neg]
  have hν' : (ν:ℂ) ≠ 0 := by exact_mod_cast hν
  field_simp
  ring_nf
  simp [I_sq]
  ring

theorem hopping_difference_product {f g : ℝ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (ν s : ℝ) :
    hoppingDifference ν (fun x => f x*g x) s =
      hoppingDifference ν f s*g (s+ν)+f s*hoppingDifference ν g s := by
  by_cases h : ν=0
  · simp [hoppingDifference,h,deriv_fun_mul (hf s) (hg s),div_eq_mul_inv]; ring
  · simp only [hoppingDifference,if_neg h,div_eq_mul_inv]; ring

/-- The increasing-order product of translated onsite factors. -/
def hoppingWord (a : ℝ) (B : List ℝ) (s : ℝ) : ℂ := (B.map (fun b => hoppingInterval a (s+b))).prod

theorem hopping_word_differentiable {a : ℝ} (ha : a ≠ 0) (B : List ℝ) :
    Differentiable ℝ (hoppingWord a B) := by
  induction B with
  | nil => exact differentiable_const _
  | cons b B ih =>
    intro x
    exact ((hopping_interval_shift_derivative ha b x).differentiableAt).mul (ih x)

/-- Each list is the ordered word obtained by inserting a new mark at one
position. The sum indexes all orders, also when transfers or partial sums coincide. -/
def hoppingInsert (ν : ℝ) : List ℝ → List (List ℝ)
  | [] => []
  | b::B => (b::(b+ν)::B.map (·+ν)) :: (hoppingInsert ν B).map (b::·)

theorem hopping_word_translate (a ν s : ℝ) (B : List ℝ) :
    hoppingWord a B (s+ν) = hoppingWord a (B.map (·+ν)) s := by
  simp only [hoppingWord,List.map_map,Function.comp_def,show ∀ b, s+ν+b = s+(b+ν) by intro; ring]

private theorem hopping_list_mul_sum {α : Type*} (c : ℂ) (F : α → ℂ) (l : List α) :
    c * (l.map F).sum = (l.map (fun x => c*F x)).sum := by
  induction l with
  | nil => simp
  | cons _ _ ih => simp [mul_add,ih]

theorem hopping_word_difference {a : ℝ} (ha : a ≠ 0) (ν : ℝ) (B : List ℝ) (s : ℝ) :
    hoppingDifference ν (hoppingWord a B) s =
      ((hoppingInsert ν B).map (fun bs => hoppingWord a bs s)).sum := by
  induction B with
  | nil =>
    change hoppingDifference ν (fun _ => 1) s = 0
    by_cases h : ν=0 <;> simp [hoppingDifference,h]
  | cons b B ih =>
    change hoppingDifference ν (fun x => hoppingInterval a (x+b)*hoppingWord a B x) s = _
    rw [hopping_difference_product (fun x => (hopping_interval_shift_derivative ha b x).differentiableAt)
      (hopping_word_differentiable ha B),hopping_single_difference ha,ih,
      hopping_word_translate a ν s B,hopping_list_mul_sum]
    simp [hoppingInsert,hoppingWord,List.map_map,Function.comp_def,mul_assoc,add_assoc]

end UV.SectorPlane
