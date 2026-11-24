import UV.ContinueOrderedCurrentWard

/-! Dependence on path vertices and transferred momentum in a locked sector.
The affine carrier offset contributes a common Fourier phase on the actual
ambient path. Two external unit polarizations give a quadratic soft factor. -/

noncomputable section

open MeasureTheory Finset
open scoped RealInnerProductSpace

namespace UV.SectorPlane.OrderedTwoBandPath

variable {A : Type*} [TopologicalSpace A]

private theorem continuous_chart {t : A → ℝ} {x : A → Spatial} (ht : Continuous t) (hx : Continuous x) :
    Continuous (fun y => thinSpatialPoint (t y) (x y)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp
  apply continuous_pi
  intro i
  cases i using Fin.cases with
  | zero => exact ht
  | succ j => exact (PiLp.continuous_apply 2 _ j).comp hx

/-- Joint continuity over a family of closed paths of the same hop count and
any continuous transfer. Both directed integration endpoints may move. -/
theorem continuous_density_vertices {P : A → OrderedTwoBandPath} {N : ℕ}
    (hn : ∀ y, (P y).hops = N) (ht : ∀ j, Continuous fun y => (P y).time j)
    (hx : ∀ j, Continuous fun y => (P y).position j)
    {ω : A → ℝ} {p : A → Spatial} (hω : Continuous ω) (hp : Continuous p) :
    Continuous (fun y => (P y).density (ω y) (p y)) := by
  let F := fun y (t : ℝ) => Complex.exp (Complex.I*(ω y:ℂ)*(t:ℂ))
  have hf : Continuous (Function.uncurry F) := by
    change Continuous (fun yt : A × ℝ => Complex.exp (Complex.I*(ω yt.1:ℂ)*(yt.2:ℂ)))
    fun_prop
  have hprimitive (j : ℕ) : Continuous (fun y => ∫ t in (0:ℝ)..(P y).time j, F y t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf (ht j)
  have hPulse (j : ℕ) : Continuous (fun y => (P y).pulse j (ω y)) := by
    have he (y : A) : (P y).pulse j (ω y) =
        (∫ t in (0:ℝ)..(P y).time (j+1), F y t) - ∫ t in (0:ℝ)..(P y).time j, F y t := by
      have hc : Continuous (F y) := by unfold F; fun_prop
      exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
    simpa only [he] using (hprimitive (j+1)).sub (hprimitive j)
  simp only [density,hn]
  apply continuous_finset_sum
  intro j _
  exact (show Continuous (fun y => spatialWave (p y) ((P y).position j)) by unfold spatialWave; fun_prop).mul (hPulse j)

theorem continuous_spatialCurrent_vertices {P : A → OrderedTwoBandPath} {N : ℕ}
    (hn : ∀ y, (P y).hops = N) (ht : ∀ j, Continuous fun y => (P y).time j)
    (hx : ∀ j, Continuous fun y => (P y).position j)
    {ω : A → ℝ} {p v : A → Spatial} (hω : Continuous ω) (hp : Continuous p) (hv : Continuous v) :
    Continuous (fun y => (P y).spatialCurrent (ω y) (p y) (v y)) := by
  have hs (j : ℕ) : Continuous (fun y => (P y).step j) := (hx (j+1)).sub (hx j)
  have hc (j : ℕ) : Continuous (fun y => (P y).hopWave j (ω y) (p y)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    let q := fun y => thinSpatialPoint (ω y) (p y)
    let z := fun y => thinSpatialPoint ((P y).time (j+1)) ((P y).position j)
    let d := fun y => thinSpatialPoint 0 ((P y).step j)
    change Continuous (fun yt : A × ℝ => thinPlaneWave (q yt.1) (z yt.1 + yt.2 • d yt.1))
    have hq : Continuous q := continuous_chart hω hp
    have hz : Continuous z := continuous_chart (ht _) (hx _)
    have hd : Continuous d := continuous_chart continuous_const (hs _)
    unfold thinPlaneWave
    fun_prop
  simp only [spatialCurrent,hn]
  apply continuous_finset_sum
  intro j _
  exact (Complex.continuous_ofReal.comp (hv.inner (hs j))).mul (hc j)

theorem continuous_density (P : OrderedTwoBandPath) :
    Continuous (fun z : ℝ × Spatial => P.density z.1 z.2) :=
  continuous_density_vertices (P := fun _ => P) (fun _ => rfl) (fun _ => continuous_const)
    (fun _ => continuous_const) continuous_fst continuous_snd

theorem continuous_spatialCurrent (P : OrderedTwoBandPath) (e : Spatial) :
    Continuous (fun z : ℝ × Spatial => P.spatialCurrent z.1 z.2 e) :=
  continuous_spatialCurrent_vertices (P := fun _ => P) (fun _ => rfl) (fun _ => continuous_const)
    (fun _ => continuous_const) continuous_fst continuous_snd continuous_const

theorem two_external_bound (P R : OrderedTwoBandPath) (ω : ℝ) (p : Spatial) (e f : UnitVector Spatial) :
    ‖P.spatialCurrent ω p e.val * R.spatialCurrent (-ω) (-p) f.val‖ ≤
      (3*(1+P.length)^2)*(3*(1+R.length)^2)*(ω^2+‖p‖^2) := by
  let Q := Real.sqrt (ω^2+‖p‖^2)
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hmin : min 1 Q ≤ Q := min_le_right _ _
  have h₁ := (P.polarized_bound ω p e).trans (mul_le_mul_of_nonneg_left hmin (by positivity))
  have h₂ := R.polarized_bound (-ω) (-p) f
  simp only [neg_sq,norm_neg] at h₂
  rw [norm_mul]
  have hh := mul_le_mul h₁ (h₂.trans (mul_le_mul_of_nonneg_left hmin (by positivity)))
    (norm_nonneg _) (by positivity)
  exact hh.trans_eq (by dsimp [Q]; rw [show ∀ a b r : ℝ, a*r*(b*r) = a*b*r^2 by intros; ring,
    Real.sq_sqrt (by positivity)])

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On an actual vertical link of the assigned affine plane the directed
displacement is the signed time interval times the existing unit carrier. -/
theorem vertical_displacement (P : OrderedTwoBandPath) (diamond : Plane E) (j : ℕ) :
    (diamond.embedGTL (P.time (j+1)) (P.position j)).1 -
      (diamond.embedGTL (P.time j) (P.position j)).1 = P.duration j • (diamond.poleUnit : E) :=
  diamond.locked_GT_difference _ _ _ _

/-- The literal ambient wave restricted to the locked plane factors into the
common offset phase, the temporal wave, and the spatial wave. -/
theorem locked_wave (diamond : Plane E) (ω t : ℝ) (p x : Spatial) :
    Complex.exp (Complex.I*((⟪ω • (diamond.poleUnit : E),(diamond.embedGTL t x).1⟫ + ⟪p,x⟫ : ℝ):ℂ)) =
      Complex.exp (Complex.I*(ω:ℂ)*(diamond.b_s:ℂ)) *
        (Complex.exp (Complex.I*(ω:ℂ)*(t:ℂ))*spatialWave p x) := by
  rw [diamond.affine_fourier_pairing,Plane.poleUnit,real_inner_smul_right,diamond.inner_carrier_self,mul_one]
  simp only [spatialWave,←Complex.exp_add,Complex.ofReal_add,Complex.ofReal_mul]
  congr 1
  ring

theorem locked_density (P : OrderedTwoBandPath) (diamond : Plane E) (ω : ℝ) (p : Spatial) :
    (∑ j ∈ range P.hops, ∫ t in P.time j..P.time (j+1), Complex.exp (Complex.I*
      ((⟪ω • (diamond.poleUnit : E), (diamond.embedGTL t (P.position j)).1⟫ +
        ⟪p,P.position j⟫ : ℝ):ℂ))) = Complex.exp (Complex.I*(ω:ℂ)*(diamond.b_s:ℂ))*P.density ω p := by
  simp only [locked_wave,intervalIntegral.integral_const_mul,intervalIntegral.integral_mul_const,density,mul_sum]
  exact sum_congr rfl fun j _ => by unfold pulse; ring

end UV.SectorPlane.OrderedTwoBandPath
