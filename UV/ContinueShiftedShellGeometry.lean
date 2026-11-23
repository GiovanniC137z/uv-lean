import UV.ContinueShiftedPole
import UV.AdvanceStableCartesian

/-! Two on-shell tests on the intrinsic Lorentzian momentum chart of
one sector plane. The rest-frame transfer uses the norm-one axial
direction and its prescribed symmetric routing. -/

noncomputable section

namespace UV.SectorPlane

open MeasureTheory
open scoped Topology InnerProductSpace UV.SectorPlane

def axialTransfer (t : ℝ) : MassiveMomentum :=
  t • WithLp.ofLp coneAxialUnit.val

theorem axial_transfer_coordinates (t : ℝ) : axialTransfer t = (t, 0) := by
  simp [axialTransfer, coneAxialUnit]

/-- At nonzero rest energy the coincident zeros of the two equal-mass
denominators lie on the axial-origin slice at the indicated radius. -/
theorem symmetric_rest_shell_intersection (m t : ℝ) (ht : t ≠ 0) (q : MassiveMomentum) :
    (shiftedD m (axialTransfer (t/2)) q = 0 ∧ shiftedD m (axialTransfer (-(t/2))) q = 0) ↔
      q.1 = 0 ∧ ‖q.2‖ ^ 2 = (t/2)^2-m^2 := by
  simp only [axial_transfer_coordinates, shiftedD, massiveD, shellSquare, Prod.fst_add,
    Prod.snd_add, add_zero]
  constructor
  · rintro ⟨h₁,h₂⟩
    have he : q.1 * t = 0 := by linarith [show (q.1+t/2)^2-(q.1+ -(t/2))^2 = 2*(q.1*t) by ring]
    have hz := (mul_eq_zero.mp he).resolve_right ht
    refine ⟨hz,?_⟩
    rw [hz,zero_add] at h₁
    linarith
  · rintro ⟨hq,hs⟩
    rw [hq,zero_add,zero_add,hs]
    constructor <;> ring

theorem symmetric_rest_shell_exists_iff {m t : ℝ} (hm : 0 ≤ m) (ht : t ≠ 0) :
    (∃ q : MassiveMomentum,
      shiftedD m (axialTransfer (t/2)) q = 0 ∧ shiftedD m (axialTransfer (-(t/2))) q = 0) ↔
      2 * m ≤ |t| := by
  constructor
  · rintro ⟨q,hq⟩
    have h := (symmetric_rest_shell_intersection m t ht q).mp hq
    have hb : m^2 ≤ (|t|/2)^2 := by
      rw [div_pow,sq_abs]
      nlinarith only [h.2,sq_nonneg ‖q.2‖]
    have hc := (sq_le_sq₀ hm (by positivity : 0 ≤ |t|/2)).mp hb
    linarith
  · intro h
    have hm' : m ≤ |t|/2 := by linarith
    have hb := (sq_le_sq₀ hm (by positivity : 0 ≤ |t|/2)).mpr hm'
    rw [div_pow,sq_abs,← div_pow] at hb
    let v : UnitVector Spatial := ⟨EuclideanSpace.single (0 : Fin 3) (1:ℝ),by simp⟩
    let r := Real.sqrt ((t/2)^2-m^2)
    refine ⟨(0,r • v.val),(symmetric_rest_shell_intersection m t ht _).mpr ⟨rfl,?_⟩⟩
    change ‖r • v.val‖^2 = _
    rw [norm_smul,v.property,mul_one,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (sub_nonneg.mpr hb)]

/-- The massive rest-frame poles cannot coincide below twice the mass. -/
theorem symmetric_rest_shell_separated {m t : ℝ} (hm : 0 ≤ m) (ht : t ≠ 0)
    (hbelow : |t| < 2 * m) (q : MassiveMomentum) :
    shiftedD m (axialTransfer (t/2)) q ≠ 0 ∨ shiftedD m (axialTransfer (-(t/2))) q ≠ 0 := by
  by_cases h₁ : shiftedD m (axialTransfer (t/2)) q = 0
  · exact Or.inr fun h₂ => hbelow.not_ge ((symmetric_rest_shell_exists_iff hm ht).mp ⟨q,h₁,h₂⟩)
  · exact Or.inl h₁

/-- The two routed energies on the common shell have opposite signs.
The normalization is the original axial sign of each running unit. -/
theorem symmetric_rest_shell_running_signs (m : ℝ) {t : ℝ} (ht : 0 < t) (q : MassiveMomentum)
    (h₁ : shiftedD m (axialTransfer (t/2)) q = 0)
    (h₂ : shiftedD m (axialTransfer (-(t/2))) q = 0) :
    axialSign (q+axialTransfer (t/2)).1 = 1 ∧
      axialSign (q+axialTransfer (-(t/2))).1 = -1 := by
  have hz := ((symmetric_rest_shell_intersection m t ht.ne' q).mp ⟨h₁,h₂⟩).1
  have hf : 0 < t/2 := half_pos ht
  simp [axial_transfer_coordinates, hz, axialSign, hf, (neg_lt_zero.mpr hf), hf.le]

theorem symmetric_rest_separated_product_distribution {E : Type*} [NormedAddCommGroup E]
    (diamond : Plane E) (ε₁ ε₂ : Evolution) (K : TopologicalSpace.Compacts MassiveMomentum)
    {m t : ℝ} (hm : 0 ≤ m) (ht : t ≠ 0) (hbelow : |t| < 2 * m)
    (U : ℝ → MassiveMomentum → ℂ) (hU : ContDiff ℝ 2 (Function.uncurry U)) :
    ∃ T : CompactMomentumTest K →L[ℂ] ℂ, ∀ f : CompactMomentumTest K,
      Filter.Tendsto (fun h : Height => ∫ q, f.value q * (U h q *
        (diamond.poleCoefficient ε₁ h (shiftedD m (axialTransfer (t/2)) q) *
         diamond.poleCoefficient ε₂ h (shiftedD m (axialTransfer (-(t/2))) q))))
        poleBoundaryHeights (𝓝 (T f)) :=
  diamond.shifted_separated_product_distribution ε₁ ε₂ K _ _ hm hm
    (fun q _ => symmetric_rest_shell_separated hm ht hbelow q) U hU

/-- With unequal masses, the common axial coordinate and the transverse
radius are fixed by the same symmetric shift on the intrinsic chart. -/
theorem symmetric_rest_shell_coordinates (m₁ m₂ t : ℝ) (ht : t ≠ 0) (q : MassiveMomentum) :
    (shiftedD m₁ (axialTransfer (t/2)) q = 0 ∧ shiftedD m₂ (axialTransfer (-(t/2))) q = 0) ↔
      q.1 = (m₁^2-m₂^2)/(2*t) ∧
      ‖q.2‖^2 = ((t^2-(m₁+m₂)^2)*(t^2-(m₁-m₂)^2))/(4*t^2) := by
  simp only [shiftedD,axial_transfer_coordinates,massiveD,shellSquare,Prod.fst_add,Prod.snd_add,add_zero]
  let a := (m₁^2-m₂^2)/(2*t)
  let R := ((t^2-(m₁+m₂)^2)*(t^2-(m₁-m₂)^2))/(4*t^2)
  have h₁ : (a+t/2)^2-m₁^2 = R := by
    dsimp only [a,R]
    field_simp
    ring
  have h₂ : (a+ -(t/2))^2-m₂^2 = R := by
    dsimp only [a,R]
    field_simp
    ring
  constructor
  · rintro ⟨hp,hm⟩
    have hdiff : q.1 * (2*t) = m₁^2-m₂^2 := by
      linarith [show (q.1+t/2)^2-(q.1+ -(t/2))^2 = q.1*(2*t) by ring]
    have ha : q.1 = a := (eq_div_iff (mul_ne_zero two_ne_zero ht)).mpr hdiff
    rw [ha] at hp
    exact ⟨ha,by linarith only [hp,h₁]⟩
  · rintro ⟨ha,hr⟩
    change q.1 = a at ha
    change ‖q.2‖^2 = R at hr
    rw [ha,hr]
    exact ⟨by linarith only [h₁],by linarith only [h₂]⟩

private theorem rest_radial_square_sign {m₁ m₂ t : ℝ} (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (ht : t ≠ 0) :
    0 ≤ ((t^2-(m₁+m₂)^2)*(t^2-(m₁-m₂)^2))/(4*t^2) ↔
      m₁+m₂ ≤ |t| ∨ |t| ≤ |m₁-m₂| := by
  have hpos : 0 < 4*t^2 := mul_pos (by norm_num) (sq_pos_of_ne_zero ht)
  have hmass : (m₁-m₂)^2 ≤ (m₁+m₂)^2 := by nlinarith only [mul_nonneg h₁ h₂]
  have h : 0 ≤ (t^2-(m₁+m₂)^2)*(t^2-(m₁-m₂)^2) ↔
      (m₁+m₂)^2 ≤ t^2 ∨ t^2 ≤ (m₁-m₂)^2 := by
    rw [mul_nonneg_iff]
    constructor
    · rintro (⟨a,_⟩ | ⟨_,b⟩)
      · exact Or.inl (sub_nonneg.mp a)
      · exact Or.inr (sub_nonpos.mp b)
    · rintro (a | b)
      · exact Or.inl ⟨sub_nonneg.mpr a,sub_nonneg.mpr (hmass.trans a)⟩
      · exact Or.inr ⟨sub_nonpos.mpr (b.trans hmass),sub_nonpos.mpr b⟩
  rw [le_div_iff₀ hpos,zero_mul,h,← sq_abs t,← sq_abs (m₁-m₂),
    sq_le_sq₀ (add_nonneg h₁ h₂) (abs_nonneg t),sq_le_sq₀ (abs_nonneg t) (abs_nonneg (m₁-m₂))]

/-- The symmetric rest routing separates unequal-mass shells exactly
between the difference and sum of the two masses. -/
theorem symmetric_rest_unequal_shell_exists_iff {m₁ m₂ t : ℝ}
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (ht : t ≠ 0) :
    (∃ q : MassiveMomentum,
      shiftedD m₁ (axialTransfer (t/2)) q = 0 ∧ shiftedD m₂ (axialTransfer (-(t/2))) q = 0) ↔
      m₁+m₂ ≤ |t| ∨ |t| ≤ |m₁-m₂| := by
  rw [← rest_radial_square_sign h₁ h₂ ht]
  constructor
  · rintro ⟨q,hq⟩
    rw [← ((symmetric_rest_shell_coordinates m₁ m₂ t ht q).mp hq).2]
    exact sq_nonneg _
  · intro h
    let v : UnitVector Spatial := ⟨EuclideanSpace.single (0 : Fin 3) (1:ℝ),by simp⟩
    let r := Real.sqrt (((t^2-(m₁+m₂)^2)*(t^2-(m₁-m₂)^2))/(4*t^2))
    refine ⟨((m₁^2-m₂^2)/(2*t),r • v.val),(symmetric_rest_shell_coordinates m₁ m₂ t ht _).mpr ⟨rfl,?_⟩⟩
    change ‖r • v.val‖^2 = _
    rw [norm_smul,v.property,mul_one,Real.norm_eq_abs,sq_abs,Real.sq_sqrt h]

theorem shell_square_add (q k : MassiveMomentum) :
    shellSquare (q+k).1 (q+k).2 = shellSquare q.1 q.2 + 2 * coneCovector q k + shellSquare k.1 k.2 := by
  simp only [Prod.fst_add,Prod.snd_add,shellSquare,norm_add_sq_real,coneCovector_apply]
  ring

/-- The Lorentzian contraction of a timelike momentum and any nonzero
real null momentum cannot vanish. The actual transverse norm and
covariant momentum slots enter the inequality. -/
theorem timelike_nonzero_null_contraction {q k : MassiveMomentum}
    (hq : 0 < shellSquare q.1 q.2) (hk : shellSquare k.1 k.2 = 0) (hn : k ≠ 0) :
    coneCovector q k ≠ 0 := by
  have hr : |k.1| = ‖k.2‖ := (sq_eq_sq₀ (abs_nonneg _) (norm_nonneg _)).mp (by
    rw [sq_abs]; exact sub_eq_zero.mp hk)
  have hp : 0 < ‖k.2‖ := by
    by_contra! h
    have hs : k.2 = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    have ht : k.1 = 0 := abs_eq_zero.mp (hr.trans (by simp [hs]))
    exact hn (Prod.ext ht hs)
  have hq' : ‖q.2‖ < |q.1| := by
    apply (sq_lt_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs]
    exact sub_pos.mp hq
  intro hh
  have he : q.1 * k.1 = ⟪q.2,k.2⟫_ℝ := sub_eq_zero.mp (by rwa [coneCovector_apply] at hh)
  have hi := abs_real_inner_le_norm q.2 k.2
  rw [← he,abs_mul,hr] at hi
  exact (not_lt_of_ge hi) (mul_lt_mul_of_pos_right hq' hp)

theorem equal_mass_null_transfer_separated {m : ℝ} (hm : 0 < m)
    {k : MassiveMomentum} (hk : shellSquare k.1 k.2 = 0) (hn : k ≠ 0) (q : MassiveMomentum) :
    shiftedD m 0 q ≠ 0 ∨ shiftedD m k q ≠ 0 := by
  by_cases hx : shiftedD m 0 q = 0
  · right
    intro hy
    have h₁ : shellSquare q.1 q.2 = m^2 := sub_eq_zero.mp (by simpa only [shiftedD,massiveD,add_zero] using hx)
    have h₂ : shellSquare (q+k).1 (q+k).2 = m^2 := sub_eq_zero.mp hy
    rw [shell_square_add,h₁,hk] at h₂
    exact timelike_nonzero_null_contraction (h₁ ▸ sq_pos_of_pos hm) hk hn (by linarith)
  · exact Or.inl hx

end UV.SectorPlane
