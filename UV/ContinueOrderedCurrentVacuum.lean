import UV.ContinueSourceReviewPulse
import UV.ContinueOrderedCurrentOnsite

/-! The prepared filled onsite vacuum at zero hopping. The spatial scalar
acts identically on the two slots and may mix arbitrarily many spatial
orbitals inside a slot. The occupation-space representation implements the
subtraction of the occupied diagonal and the constant vacuum energy. -/

noncomputable section

open MeasureTheory Set Filter Matrix
open scoped Topology ComplexConjugate ENNReal

namespace UV.SectorPlane

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Fill every negative slot, leaving every positive slot empty. -/
def orderedOnsiteSea (band : ι → Bool) : Finset ι := Finset.univ.filter (fun i => band i = false)

def orderedOnsiteEnergy (m : ℝ) (band : ι → Bool) (i : ι) : ℝ := if band i then m else -m

/-- Multiplication by a scalar at one spatial slice is diagonal in the slot, including
after an arbitrary finite spatial compression. The Euclidean coefficient is i q. -/
def orderedOnsiteScalar (q : ℝ) (band : ι → Bool) (B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if band i = band j then Complex.I*(q:ℂ)*B i j else 0

private theorem sea_current_transpose (S : Finset ι) (B : Matrix ι ι ℂ) :
    seaCurrent S B.transpose = (seaCurrent S B).transpose := by
  ext X Y
  change (∑ a, ∑ b, seaCurrentEntry B.transpose X Y a b) - _ =
    (∑ a, ∑ b, seaCurrentEntry B Y X a b) - _
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    unfold seaCurrentEntry
    by_cases h : b ∈ X ∧ a ∈ Y ∧ X.erase b = Y.erase a
    · rw [if_pos h,if_pos ⟨h.2.1,h.1,h.2.2.symm⟩]
      simp only [Matrix.transpose_apply]
      ring
    · rw [if_neg h,if_neg (fun hh => h ⟨hh.2.1,hh.1,hh.2.2.symm⟩)]
  · by_cases h : X=Y <;> simp [h,Ne.symm]

theorem orderedOnsite_charge_annihilates (q : ℝ) (band : ι → Bool) (B : Matrix ι ι ℂ) (X : Finset ι) :
    seaCurrent (orderedOnsiteSea band) (orderedOnsiteScalar q band B) X (orderedOnsiteSea band) = 0 ∧
      seaCurrent (orderedOnsiteSea band) (orderedOnsiteScalar q band B) (orderedOnsiteSea band) X = 0 := by
  let S := orderedOnsiteSea band
  let Q := orderedOnsiteScalar q band B
  have hentry (i j : ι) (hi : i ∉ S) (hj : j ∈ S) : band i ≠ band j := by
    simpa [S,orderedOnsiteSea] using fun h => hi (by simpa [S,orderedOnsiteSea,h] using hj)
  constructor
  · apply (sea_current_annihilates_iff S Q).2 ((sea_offblock S Q).2 (fun i hi j hj => if_neg (hentry i j hi hj)))
  · change (seaCurrent S Q).transpose X S = 0
    rw [←sea_current_transpose]
    apply (sea_current_annihilates_iff S Q.transpose).2 ((sea_offblock S Q.transpose).2
      (fun i hi j hj => if_neg (Ne.symm (hentry i j hi hj))))

def orderedOnsiteHamiltonian (m q : ℝ) (band : ι → Bool) (B : Matrix ι ι ℂ) :
    Matrix (Finset ι) (Finset ι) ℂ :=
  seaFreeGenerator (orderedOnsiteSea band) (orderedOnsiteEnergy m band) +
    seaCurrent (orderedOnsiteSea band) (orderedOnsiteScalar q band B)

theorem orderedOnsite_hamiltonian_annihilates (m q : ℝ) (band : ι → Bool) (B : Matrix ι ι ℂ) (X : Finset ι) :
    orderedOnsiteHamiltonian m q band B X (orderedOnsiteSea band) = 0 ∧
      orderedOnsiteHamiltonian m q band B (orderedOnsiteSea band) X = 0 := by
  obtain ⟨hc,hr⟩ := orderedOnsite_charge_annihilates q band B X
  by_cases h : X = orderedOnsiteSea band
  · subst X
    simp [orderedOnsiteHamiltonian,seaFreeGenerator,hc]
  · simp [orderedOnsiteHamiltonian,seaFreeGenerator,h,Ne.symm h,hc,hr]

/-- The constant vacuum vector solves the original finite occupation-space Volterra
equation. Any solution has the same vacuum amplitude; this uses both the vacuum ket
and bra and does not require calling the anti-Hermitian i q term Hermitian. -/
theorem orderedOnsite_evolution (m q : ℝ) (band : ι → Bool) (B : ℝ → Matrix ι ι ℂ) (T : ℝ) :
    let S := orderedOnsiteSea band
    let E := orderedOnsiteEnergy m band
    let Q := fun t => orderedOnsiteScalar q band (B t)
    SeaIntegralEvolution S E Q (fun _ X => if X=S then 1 else 0) T ∧
    ∀ ψ, SeaIntegralEvolution S E Q ψ T → ∀ t ∈ Icc 0 T, ψ t S = 1 := by
  intro S E Q
  constructor
  · intro t _ X
    have hz (s : ℝ) : ((seaFreeGenerator S E + seaCurrent S (Q s)) *ᵥ
        (fun Y => if Y=S then (1:ℂ) else 0)) X = 0 := by
      change ∑ Y, orderedOnsiteHamiltonian m q band (B s) X Y * (if Y=S then (1:ℂ) else 0) = 0
      simpa [mul_ite] using (orderedOnsite_hamiltonian_annihilates m q band (B s) X).1
    simp only [hz,intervalIntegral.integral_zero,sub_zero]
  · intro ψ hψ t ht
    have hz (s : ℝ) : ((seaFreeGenerator S E + seaCurrent S (Q s)) *ᵥ ψ s) S = 0 := by
      change ∑ Y, orderedOnsiteHamiltonian m q band (B s) S Y * ψ s Y = 0
      exact Finset.sum_eq_zero fun Y _ => by rw [(orderedOnsite_hamiltonian_annihilates m q band (B s) Y).2,zero_mul]
    rw [hψ t ht S]
    simp [hz]

/-- Actual compressed spatial matrix entries against the harmonic spatial readout
(or any bounded real profile). Positive and negative orbitals may use the same
spatial basis; the Kronecker factor in the slot is supplied by orderedOnsiteScalar. -/
def orderedOnsiteSpatialMatrix {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (orb : ι → Ω → ℂ) (φ : Ω → ℝ) : Matrix ι ι ℂ :=
  fun i j => ∫ x, conj (orb i x)*((φ x : ℝ):ℂ)*orb j x ∂μ

omit [Fintype ι] [LinearOrder ι] in
theorem orderedOnsite_spatial_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {orb : ι → Ω → ℂ} (hOrb : ∀ i, MemLp (orb i) 2 μ) {φ : Ω → ℝ} (hφ : MemLp φ ∞ μ) (i j : ι) :
    Integrable (fun x => conj (orb i x)*((φ x : ℝ):ℂ)*orb j x) μ := by
  have h := (hOrb i).star.integrable_mul (show MemLp (fun x => (φ x:ℂ)*orb j x) 2 μ from (hOrb j).mul' hφ.ofReal)
  simpa only [mul_assoc] using h

/-- The ordered expansion of the time-dependent generator acting on the prepared
vacuum. All nonconstant states are exactly zero for all time profiles. -/
def orderedOnsiteDyson (m q : ℝ) (band : ι → Bool) (B : ℝ → Matrix ι ι ℂ) (a : ℝ) :
    ℕ → ℝ → Finset ι → ℂ
  | 0, _, X => if X = orderedOnsiteSea band then 1 else 0
  | n+1, t, X => -∫ s in a..t, (orderedOnsiteHamiltonian m q band (B s) *ᵥ orderedOnsiteDyson m q band B a n s) X

theorem orderedOnsite_dyson_positive (m q : ℝ) (band : ι → Bool) (B : ℝ → Matrix ι ι ℂ) (a : ℝ) (n : ℕ) :
    ∀ t X, orderedOnsiteDyson m q band B a (n+1) t X = 0 := by
  induction n with
  | zero =>
    intro t X
    have hz (s : ℝ) : (orderedOnsiteHamiltonian m q band (B s) *ᵥ orderedOnsiteDyson m q band B a 0 s) X = 0 := by
      simpa [orderedOnsiteDyson,Matrix.mulVec,dotProduct,mul_ite] using (orderedOnsite_hamiltonian_annihilates m q band (B s) X).1
    rw [orderedOnsiteDyson]
    simp only [hz,intervalIntegral.integral_zero,neg_zero]
  | succ n ih =>
    intro t X
    have hz (s : ℝ) : orderedOnsiteDyson m q band B a (n+1) s = 0 := funext (ih s)
    rw [orderedOnsiteDyson]
    simp only [hz,Matrix.mulVec_zero,Pi.zero_apply,intervalIntegral.integral_zero,neg_zero]

def orderedOnsiteAmplitude (m q : ℝ) (band : ι → Bool) (B : ℝ → Matrix ι ι ℂ) (a t : ℝ) : ℂ :=
  ∑' n, orderedOnsiteDyson m q band B a n t (orderedOnsiteSea band)

theorem orderedOnsite_amplitude_one (m q : ℝ) (band : ι → Bool) (B : ℝ → Matrix ι ι ℂ) (a t : ℝ) :
    orderedOnsiteAmplitude m q band B a t = 1 := by
  unfold orderedOnsiteAmplitude
  rw [tsum_eq_single 0 (fun n hn => by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact orderedOnsite_dyson_positive m q band B a k _ _)]
  simp [orderedOnsiteDyson]

/-- Any net of finite orbital cutoffs and vacuum slab endpoints has the same
amplitude. This is a limit of scalar vacuum matrix elements. -/
theorem orderedOnsite_cutoff_vacuum {K : Type*} (l : Filter K) (n : K → ℕ)
    (m q : ℝ) (band : (k : K) → Fin (n k) → Bool)
    (B : (k : K) → ℝ → Matrix (Fin (n k)) (Fin (n k)) ℂ) (a t : K → ℝ) :
    Tendsto (fun k => orderedOnsiteAmplitude m q (band k) (B k) (a k) (t k)) l (𝓝 1) := by
  simp only [orderedOnsite_amplitude_one]
  exact tendsto_const_nhds

omit [LinearOrder ι] in
theorem orderedOnsite_occupied_energy (m : ℝ) (band : ι → Bool) :
    (∑ i ∈ orderedOnsiteSea band, orderedOnsiteEnergy m band i) =
      -(m * ((orderedOnsiteSea band).card:ℝ)) := by
  calc
    _ = ∑ _i ∈ orderedOnsiteSea band, -m := Finset.sum_congr rfl (fun i hi => by
      have hb : band i = false := (Finset.mem_filter.mp hi).2
      simp [orderedOnsiteEnergy,hb])
    _ = _ := by simp [mul_comm]

/-- Before subtracting the trace of the occupied orbitals, the scalar second
quantization acts on the vacuum by precisely that trace. This derives the
phase removed by the normal-ordering prescription. -/
theorem orderedOnsite_bare_scalar_vacuum (q : ℝ) (band : ι → Bool) (B : Matrix ι ι ℂ) (X : Finset ι) :
    let S := orderedOnsiteSea band
    let Q := orderedOnsiteScalar q band B
    (∑ i, ∑ j, Q i j • ((seaAnnihilate i)ᴴ * seaAnnihilate j)) X S =
      (if X=S then ∑ i ∈ S, Q i i else 0) := by
  intro S Q
  have h := (orderedOnsite_charge_annihilates q band B X).1
  change seaCurrent S Q X S = 0 at h
  rw [sea_current_second_quantization,Matrix.sub_apply,sub_eq_zero] at h
  rw [h]
  by_cases he : X=S <;> simp [Matrix.smul_apply,he]

omit [Fintype ι] [LinearOrder ι] in
theorem orderedOnsite_spatial_hermitian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (orb : ι → Ω → ℂ) (φ : Ω → ℝ) : (orderedOnsiteSpatialMatrix μ orb φ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change conj (∫ x, conj (orb j x)*(φ x:ℂ)*orb i x ∂μ) =
    ∫ x, conj (orb i x)*(φ x:ℂ)*orb j x ∂μ
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul,Complex.conj_ofReal,starRingEnd_self_apply]
  ring

/-- With a spatial multiplier already smeared at each time, the exact filled
vacuum amplitude is independent of the field, even before any derivative. -/
theorem orderedOnsite_smeared_vacuum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (orb : ι → Ω → ℂ) (m q a t : ℝ) (band : ι → Bool) :
    (fun φ : ℝ → Ω → ℝ => orderedOnsiteAmplitude m q band
      (fun s => orderedOnsiteSpatialMatrix μ orb (φ s)) a t) = fun _ => (1:ℂ) :=
  funext fun _ => orderedOnsite_amplitude_one ..

end UV.SectorPlane
