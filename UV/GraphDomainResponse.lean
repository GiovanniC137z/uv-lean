import UV.Response
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section

namespace UV

variable {H D K : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- The graph-domain Neumann bound also handles a zero-dimensional domain;
the nontrivial case is the normed-ring geometric-series theorem. -/
theorem graph_domain_neumann_bound {t : D →L[ℂ] D} {q : ℝ}
    (ht : ‖t‖ ≤ q) (hq : q < 1) :
    IsUnit (1 - t) ∧ ‖Ring.inverse (1 - t)‖ ≤ 1 / (1 - q) := by
  cases subsingleton_or_nontrivial D with
  | inl hD =>
    letI := hD
    have ht0 : t = 0 := Subsingleton.elim _ _
    rw [ht0, sub_zero]
    refine ⟨isUnit_one, ?_⟩
    rw [Ring.inverse_one]
    have h1 : (1 : D →L[ℂ] D) = 0 := Subsingleton.elim _ _
    rw [h1, norm_zero]
    exact div_nonneg zero_le_one (sub_pos.mpr hq).le
  | inr hD =>
    letI := hD
    exact response_inverse_one_sub_bound ht hq

/-- The Neumann construction takes place in endomorphisms of the graph domain,
then maps the physical Hilbert space back to that domain. -/
def graphDomainResolvent (RY : H ≃L[ℂ] D) (δ : D →L[ℂ] H) : H →L[ℂ] D :=
  (Ring.inverse (1 - RY.toContinuousLinearMap.comp δ)).comp RY.toContinuousLinearMap

/-- A certified approximate graph-domain inverse constructs an actual exact
continuous linear equivalence. No inverse of the perturbed pencil is assumed. -/
theorem graph_domain_inverse_certification
    (A : D →L[ℂ] H) (RY : H ≃L[ℂ] D)
    (hA : A = RY.symm.toContinuousLinearMap) (δ : D →L[ℂ] H)
    {B ε : ℝ} (hB : ‖RY.toContinuousLinearMap‖ ≤ B) (hε : ‖δ‖ ≤ ε)
    (hq : B * ε < 1) :
    ∃ RX : H ≃L[ℂ] D,
      RX.toContinuousLinearMap = graphDomainResolvent RY δ ∧
      RX.symm.toContinuousLinearMap = A - δ ∧
      RX.toContinuousLinearMap.comp (A - δ) = ContinuousLinearMap.id ℂ D ∧
      (A - δ).comp RX.toContinuousLinearMap = ContinuousLinearMap.id ℂ H ∧
      ‖RX.toContinuousLinearMap‖ ≤ B / (1 - B * ε) ∧
      ‖RX.toContinuousLinearMap - RY.toContinuousLinearMap‖ ≤ B ^ 2 * ε / (1 - B * ε) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hden : 0 < 1 - B * ε := sub_pos.mpr hq
  let t := RY.toContinuousLinearMap.comp δ
  let T : D →L[ℂ] D := 1 - t
  have ht : ‖t‖ ≤ B * ε :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hB hε (norm_nonneg _) hB0)
  obtain ⟨hu, hnorm⟩ := graph_domain_neumann_bound ht hq
  have hleftT : (Ring.inverse T).comp T = ContinuousLinearMap.id ℂ D :=
    Ring.inverse_mul_cancel T hu
  have hrightT : T.comp (Ring.inverse T) = ContinuousLinearMap.id ℂ D :=
    Ring.mul_inverse_cancel T hu
  have hfactor : A - δ = A.comp T := by
    ext x
    simp [T, t, hA]
  let RXmap := graphDomainResolvent RY δ
  have hleft : RXmap.comp (A - δ) = ContinuousLinearMap.id ℂ D := by
    ext x
    have h := congrArg (fun f : D →L[ℂ] D => f x) hleftT
    simpa [RXmap, graphDomainResolvent, ← hfactor, hA, T, t] using h
  have hright : (A - δ).comp RXmap = ContinuousLinearMap.id ℂ H := by
    ext x
    have h := congrArg (fun f : D →L[ℂ] D => RY.symm (f (RY x))) hrightT
    simpa [RXmap, graphDomainResolvent, hfactor, hA, T, t] using h
  let RX := ContinuousLinearEquiv.equivOfInverse' RXmap (A - δ) hleft hright
  have hRX : RX.toContinuousLinearMap = RXmap := rfl
  have hRXinv : RX.symm.toContinuousLinearMap = A - δ := rfl
  have hRXnorm : ‖RXmap‖ ≤ B / (1 - B * ε) := by
    calc
      _ ≤ ‖Ring.inverse T‖ * ‖RY.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 / (1 - B * ε)) * B := mul_le_mul hnorm hB (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hdiff : RXmap - RY.toContinuousLinearMap = RXmap.comp (δ.comp RY.toContinuousLinearMap) := by
    ext x
    have h := congrArg (fun f : D →L[ℂ] D => f (RY x)) hleft
    change RXmap ((A - δ) (RY x)) = RY x at h
    rw [ContinuousLinearMap.sub_apply, hA] at h
    change RXmap (RY.symm (RY x) - δ (RY x)) = RY x at h
    rw [RY.symm_apply_apply, map_sub] at h
    change RXmap x - RY x = RXmap (δ (RY x))
    calc
      RXmap x - RY x = RXmap x - (RXmap x - RXmap (δ (RY x))) :=
        congrArg (fun y => RXmap x - y) h.symm
      _ = _ := by abel
  have hdiffnorm : ‖RXmap - RY.toContinuousLinearMap‖ ≤ B ^ 2 * ε / (1 - B * ε) := by
    rw [hdiff]
    calc
      _ ≤ ‖RXmap‖ * (‖δ‖ * ‖RY.toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ (B / (1 - B * ε)) * (ε * B) := by gcongr
      _ = _ := by ring
  exact ⟨RX, hRX, hRXinv, hleft, hright, hRXnorm, hdiffnorm⟩

/-- The generalized two-space inverse agrees with the constructed equivalence,
so its norm bounds concern an actual inverse, not a default value. -/
theorem graph_domain_inverse_bounds
    (A : D →L[ℂ] H) (RY : H ≃L[ℂ] D)
    (hA : A = RY.symm.toContinuousLinearMap) (δ : D →L[ℂ] H)
    {B ε : ℝ} (hB : ‖RY.toContinuousLinearMap‖ ≤ B) (hε : ‖δ‖ ≤ ε)
    (hq : B * ε < 1) :
    (A - δ).IsInvertible ∧ (A - δ).inverse = graphDomainResolvent RY δ ∧
      ‖(A - δ).inverse‖ ≤ B / (1 - B * ε) ∧
      ‖(A - δ).inverse - RY.toContinuousLinearMap‖ ≤ B ^ 2 * ε / (1 - B * ε) := by
  obtain ⟨RX, hRX, hRXinv, _, _, hnorm, hdiff⟩ :=
    graph_domain_inverse_certification A RY hA δ hB hε hq
  have hi : (A - δ).inverse = RX.toContinuousLinearMap := by rw [← hRXinv]; simp
  exact ⟨⟨RX.symm, hRXinv⟩, hi.trans hRX, hi ▸ hnorm, hi ▸ hdiff⟩

/-- The response maps have their graph-domain types: U maps D to the retained
space, while V maps the retained space to the electromagnetic Hilbert space. -/
theorem graph_domain_schur_error
    (A : D →L[ℂ] H) (RY : H ≃L[ℂ] D)
    (hA : A = RY.symm.toContinuousLinearMap) (δ : D →L[ℂ] H)
    {B ε : ℝ} (hB : ‖RY.toContinuousLinearMap‖ ≤ B) (hε : ‖δ‖ ≤ ε)
    (hq : B * ε < 1) (U : D →L[ℂ] K) (V : K →L[ℂ] H) :
    (A - δ).IsInvertible ∧ ‖(A - δ).inverse‖ ≤ B / (1 - B * ε) ∧
      ‖U.comp (((A - δ).inverse - RY.toContinuousLinearMap).comp V)‖ ≤
        ‖U‖ * ‖V‖ * B ^ 2 * ε / (1 - B * ε) := by
  obtain ⟨hi, _, hn, hd⟩ := graph_domain_inverse_bounds A RY hA δ hB hε hq
  refine ⟨hi, hn, ?_⟩
  calc
    _ ≤ ‖U‖ * (‖(A - δ).inverse - RY.toContinuousLinearMap‖ * ‖V‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖U‖ * ((B ^ 2 * ε / (1 - B * ε)) * ‖V‖) := by gcongr
    _ = _ := by ring

/-- The full first-order rate bound uses the same baseline functional for both
exact Schur corrections. This is the source's pole-bookkeeping family, not a
replacement of X by a scaled X inside the electromagnetic inverse. -/
theorem graph_domain_aposteriori_schur_rate
    (A : D →L[ℂ] H) (RY : H ≃L[ℂ] D)
    (hA : A = RY.symm.toContinuousLinearMap) (δ : D →L[ℂ] H)
    {B ε : ℝ} (hB : ‖RY.toContinuousLinearMap‖ ≤ B) (hε : ‖δ‖ ≤ ε)
    (hq : B * ε < 1) (D0 : H →L[ℂ] D) (U : D →L[ℂ] K) (V : K →L[ℂ] H)
    (W : K →L[ℂ] ℂ) (v : K) (denominator : ℂ) (hd : denominator ≠ 0) :
    let ΔX := -U.comp (((A - δ).inverse - D0).comp V)
    let ΔY := -U.comp ((RY.toContinuousLinearMap - D0).comp V)
    (A - δ).IsInvertible ∧ ‖(A - δ).inverse‖ ≤ B / (1 - B * ε) ∧
      ‖ΔX - ΔY‖ ≤ ‖U‖ * ‖V‖ * B ^ 2 * ε / (1 - B * ε) ∧
      |responsePoleRate W v denominator ΔX - responsePoleRate W v denominator ΔY| ≤
        2 * (‖W‖ * ‖v‖ / ‖denominator‖) *
          (‖U‖ * ‖V‖ * B ^ 2 * ε / (1 - B * ε)) := by
  dsimp only
  obtain ⟨hi, hn, hs⟩ := graph_domain_schur_error A RY hA δ hB hε hq U V
  have heq : -U.comp (((A - δ).inverse - D0).comp V) -
      -U.comp ((RY.toContinuousLinearMap - D0).comp V) =
      -U.comp (((A - δ).inverse - RY.toContinuousLinearMap).comp V) := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  have hnorm : ‖-U.comp (((A - δ).inverse - D0).comp V) -
      -U.comp ((RY.toContinuousLinearMap - D0).comp V)‖ ≤
      ‖U‖ * ‖V‖ * B ^ 2 * ε / (1 - B * ε) := by
    rw [heq, norm_neg]
    exact hs
  refine ⟨hi, hn, hnorm, ?_⟩
  exact (response_pole_rate_error W v hd _ _).trans
    (mul_le_mul_of_nonneg_left hnorm (by positivity))

/-- Inversion between two different Banach-space types is analytic on the
invertible set. A fixed local equivalence reduces it to endomorphism inversion;
no analytic approximate-inverse family is assumed. -/
theorem graph_domain_analytic_inverse
    {s : Set ℂ} {F : ℂ → D →L[ℂ] H}
    (hF : AnalyticOnNhd ℂ F s) (hinvertible : ∀ z ∈ s, (F z).IsInvertible) :
    AnalyticOnNhd ℂ (fun z => (F z).inverse) s := by
  intro z hz
  obtain ⟨e, he⟩ := hinvertible z hz
  let g : ℂ → D →L[ℂ] D := fun w => e.symm.toContinuousLinearMap.comp (F w)
  have hg : AnalyticAt ℂ g z :=
    ((ContinuousLinearMap.compL ℂ D H D e.symm.toContinuousLinearMap).analyticAt _).comp (hF z hz)
  have hgunit : IsUnit (g z) := by
    have heq : g z = 1 := by
      ext x
      change e.symm (F z x) = x
      rw [← he]
      exact e.symm_apply_apply x
    rw [heq]
    exact isUnit_one
  have hginv : AnalyticAt ℂ (fun w => Ring.inverse (g w)) z := by
    have hbase : AnalyticAt ℂ Ring.inverse (g z) := by
      simpa only [hgunit.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hgunit.unit)
    exact hbase.comp hg
  have hpost : AnalyticAt ℂ
      (fun w => (Ring.inverse (g w)).comp e.symm.toContinuousLinearMap) z :=
    ((ContinuousLinearMap.compL ℂ H D D).analyticAt_bilinear _).comp₂ hginv analyticAt_const
  have heq : (fun w => (F w).inverse) =
      (fun w => (Ring.inverse (g w)).comp e.symm.toContinuousLinearMap) := by
    funext w
    exact ContinuousLinearMap.inverse_eq_ringInverse e (F w)
  rw [heq]
  exact hpost

/-- Holomorphic exact graph-domain inverses and Schur corrections, with
pointwise quantitative bounds on the same complex domain. The inverse is
constructed by the strict error margin before analyticity is deduced. -/
theorem graph_domain_analytic_schur
    {s : Set ℂ} {A δ : ℂ → D →L[ℂ] H} {D0 : ℂ → H →L[ℂ] D}
    {U : ℂ → D →L[ℂ] K} {V : ℂ → K →L[ℂ] H}
    (RY : ℂ → H ≃L[ℂ] D) {B ε : ℝ}
    (hA : AnalyticOnNhd ℂ A s) (hδ : AnalyticOnNhd ℂ δ s)
    (hD0 : AnalyticOnNhd ℂ D0 s) (hU : AnalyticOnNhd ℂ U s) (hV : AnalyticOnNhd ℂ V s)
    (happrox : ∀ z ∈ s, A z = (RY z).symm.toContinuousLinearMap)
    (hB : ∀ z ∈ s, ‖(RY z).toContinuousLinearMap‖ ≤ B)
    (hε : ∀ z ∈ s, ‖δ z‖ ≤ ε) (hq : B * ε < 1) :
    (∀ z ∈ s, (A z - δ z).IsInvertible ∧
      ‖(A z - δ z).inverse‖ ≤ B / (1 - B * ε) ∧
      ‖(U z).comp (((A z - δ z).inverse - (RY z).toContinuousLinearMap).comp (V z))‖ ≤
        ‖U z‖ * ‖V z‖ * B ^ 2 * ε / (1 - B * ε)) ∧
    AnalyticOnNhd ℂ (fun z => (A z - δ z).inverse) s ∧
    AnalyticOnNhd ℂ (fun z => -(U z).comp (((A z - δ z).inverse - D0 z).comp (V z))) s := by
  have hcert z hz := graph_domain_schur_error (A z) (RY z) (happrox z hz)
    (δ z) (hB z hz) (hε z hz) hq (U z) (V z)
  have hinv : AnalyticOnNhd ℂ (fun z => (A z - δ z).inverse) s :=
    graph_domain_analytic_inverse (hA.sub hδ) (fun z hz => (hcert z hz).1)
  refine ⟨hcert, hinv, ?_⟩
  intro z hz
  have hinner := ((ContinuousLinearMap.compL ℂ K H D).analyticAt_bilinear _).comp₂
    ((hinv z hz).sub (hD0 z hz)) (hV z hz)
  exact (((ContinuousLinearMap.compL ℂ K D K).analyticAt_bilinear _).comp₂
    (hU z hz) hinner).fun_neg

/-- Source response-family formulation: analyticity of the approximate pencil
is derived from analytic X,Y,D₀ on the common inverse domain. No bound on the
unknown product D₀X and no exact response inverse are assumptions. -/
theorem graph_domain_response_family [CompleteSpace H]
    {s : Set ℂ} {X Y : ℂ → D →L[ℂ] H} {D0 : ℂ → H →L[ℂ] D}
    {U : ℂ → D →L[ℂ] K} {V : ℂ → K →L[ℂ] H}
    (RY : ℂ → H ≃L[ℂ] D) {B ε : ℝ}
    (hX : AnalyticOnNhd ℂ X s) (hY : AnalyticOnNhd ℂ Y s)
    (hD0 : AnalyticOnNhd ℂ D0 s) (hD0domain : ∀ z ∈ s, (D0 z).IsInvertible)
    (hU : AnalyticOnNhd ℂ U s) (hV : AnalyticOnNhd ℂ V s)
    (happrox : ∀ z ∈ s, (D0 z).inverse - Y z = (RY z).symm.toContinuousLinearMap)
    (hB : ∀ z ∈ s, ‖(RY z).toContinuousLinearMap‖ ≤ B)
    (hε : ∀ z ∈ s, ‖X z - Y z‖ ≤ ε) (hq : B * ε < 1) :
    (∀ z ∈ s, ((D0 z).inverse - X z).IsInvertible ∧
      ‖((D0 z).inverse - X z).inverse‖ ≤ B / (1 - B * ε) ∧
      ‖(U z).comp ((((D0 z).inverse - X z).inverse - (RY z).toContinuousLinearMap).comp (V z))‖ ≤
        ‖U z‖ * ‖V z‖ * B ^ 2 * ε / (1 - B * ε)) ∧
    AnalyticOnNhd ℂ (fun z => ((D0 z).inverse - X z).inverse) s ∧
    AnalyticOnNhd ℂ (fun z => -(U z).comp
      ((((D0 z).inverse - X z).inverse - D0 z).comp (V z))) s := by
  have hA := (graph_domain_analytic_inverse hD0 hD0domain).sub hY
  have h := graph_domain_analytic_schur RY hA (hX.sub hY) hD0 hU hV happrox hB hε hq
  have heq z : ((D0 z).inverse - Y z) - (X z - Y z) = (D0 z).inverse - X z := by abel
  simpa only [Pi.sub_apply, heq] using h

end UV
