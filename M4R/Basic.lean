import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Complex.Tietze
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Jacobian
-- import Mathlib.MeasureTheory.MeasureSpace
-- import Mathlib.MeasureTheory.Constructions.PiLp
variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open NNReal
open MeasureTheory MeasureTheory.Measure

-- theorem stoneweierstrass {X : Type u_1} [TopologicalSpace X] [CompactSpace X] (A : Subalgebra E C(X, E)) (w : A.SeparatesPoints) (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) :
--         ∃ (g : ↥A), ‖↑g - f‖ < ε := by sorry
-- #synth MeasureSpace (EuclideanSpace ℝ (Fin 3))

set_option linter.unnecessarySimpa false
-- set_option backward.isDefEq.respectTransparency false

-- def zero : E := 0 : E
-- {x : E // x ∈ Metric.closedBall 0 1 } → {x : E // x ∈ Metric.closedBall 0 1 }
theorem brouwer_fixed_point (f : (Metric.closedBall (0 : E) 1) → (Metric.closedBall 0 1)) (hf : Continuous f) :
    ∃ x, f x = x := by sorry


theorem restated_IoD  (f : E → E)
    (hf_cont : Continuous f) (hf_inj : Function.Injective f)
    : f 0 ∈ interior (f ''(Metric.closedBall 0 1)) := by sorry



theorem IoD2 (f : E → E)
    (hf_cont : ContinuousOn f (Metric.closedBall 0 1)) (hf_inj : Set.InjOn f (Metric.closedBall 0 1))
    : f 0 ∈ interior (f ''(Metric.closedBall 0 1)) := by
  -- let d : ℕ := Set.finrank ℝ E

  let hBn_equiv := Equiv.Set.imageOfInjOn f (Metric.closedBall 0 1) hf_inj
  let hBn_inv_cmap : C(f '' Metric.closedBall 0 1, (Metric.closedBall (0 : E) 1)) :=
  ⟨hBn_equiv.symm,  Continuous.continuous_symm_of_equiv_compact_to_t2 (continuous_induced_rng.mpr <|
    ContinuousOn.restrict hf_cont)⟩
  have hballimageclosed : IsClosed (f '' Metric.closedBall 0 1) := IsClosed.mono
    ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).isClosed fun U a ↦ a
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hballimageclosed hBn_inv_cmap
  -- clear! h_closed_image
  have hG0 : G (f 0) = (0 : E) := by
    let fzero' : (f '' Metric.closedBall (0 : E) 1) := ⟨f 0, ⟨0, by simp, rfl⟩⟩
    have := congr($hG fzero')
    conv_lhs at this => simp [fzero']
    have H : (⟨f 0, ⟨0, by simp, rfl⟩⟩ : f '' Metric.closedBall 0 1) = hBn_equiv ⟨0, by simp⟩ := Subtype.ext rfl
    simp [this, hBn_inv_cmap, fzero', H]
  have hStability_of_zero (Gtilde : E → E)
      (hGtilde : ContinuousOn Gtilde (f '' Metric.closedBall 0 1))(hy : ∀ y ∈ (f '' (Metric.closedBall 0 1)), ‖G y - Gtilde y‖ ≤ 1 ) : ∃ y ∈ f '' (Metric.closedBall 0 1), Gtilde y = 0 := by
    let diff_fun : E → E := fun x => x - Gtilde (f x)
    have hMaps_To : Set.MapsTo diff_fun (Metric.closedBall (0 : E) 1) (Metric.closedBall (0 : E) 1) := by
      intro x hx
      dsimp [diff_fun]
      have hxeq : x = G (f x) := by
        have hfx : f x ∈ f '' (Metric.closedBall 0 1) := Set.mem_image_of_mem f hx
        simp only [← G.restrict_apply_mk _ _ hfx, hG, ContinuousMap.coe_mk, hBn_inv_cmap, hBn_equiv]
        let e := Equiv.Set.imageOfInjOn f (Metric.closedBall 0 1) hf_inj
        have hfxeq : ⟨f (x : E), hfx⟩ = e ⟨x, Metric.mem_closedBall.mpr hx⟩ := SetCoe.ext rfl
        rw [hfxeq, (e.symm_apply_apply ⟨x, Metric.mem_closedBall.mpr hx⟩)]
      nth_rw 1 [hxeq]
      have h4 : f x ∈ f '' Metric.closedBall 0 1 := Set.mem_image_of_mem f hx
      apply hy (f x) at h4
      exact mem_closedBall_zero_iff.mpr h4
    have diff_fun_cont_on : ContinuousOn diff_fun (Metric.closedBall 0 1):= by
      apply ContinuousOn.sub (continuousOn_id' (Metric.closedBall 0 1))
      rw [continuousOn_iff_continuous_restrict]
      refine ContinuousOn.restrict ?_
      exact hGtilde.comp hf_cont (Set.mapsTo_image f (Metric.closedBall 0 1))




      -- exact hGtilde


      -- apply Continuous.comp
      -- ·




      -- apply ContinuousOn.sub (continuousOn_id' (Metric.closedBall 0 1)) (Continuous.comp_continuousOn' ?_ hf_cont)

    have hBrouwer := brouwer_fixed_point (Set.MapsTo.restrict diff_fun (Metric.closedBall (0 : E)  1) (Metric.closedBall 0 1) hMaps_To)
    rcases hBrouwer (ContinuousOn.mapsToRestrict diff_fun_cont_on hMaps_To) with ⟨x, hx⟩
    refine ⟨f x, ⟨⟨x ,⟨(by simpa [Metric.mem_closedBall, dist_zero_right] using mem_closedBall_zero_iff.mp x.2), rfl⟩⟩, ?_⟩⟩
    simp [diff_fun, Subtype.ext_iff] at hx
    simpa [Set.MapsTo.val_restrict_apply, sub_eq_self] using (AddOpposite.op_eq_zero_iff (Gtilde (f ↑x))).mp (congrArg AddOpposite.op hx)

  -- let ι := Module.Basis.ofVectorSpaceIndex ℝ (E)
  -- let d : ℝ := Fintype.card ι

  rcases subsingleton_or_nontrivial E with hsubsingleton | hnontrivial
  · sorry
  · by_contra hnotinterior
    have hGconton := Continuous.continuousOn (ContinuousMap.continuous G) (s := f '' (Metric.closedBall 0 1))
    -- have h8 : IsCompact (Metric.closedBall 0 1) := by exact isCompact_closedBall 0 1
    have himgcompact := IsCompact.image_of_continuousOn (isCompact_closedBall 0 1) hf_cont
    have hGuniformcont := IsCompact.uniformContinuousOn_of_continuous himgcompact hGconton
    rw [Metric.uniformContinuousOn_iff_le] at hGuniformcont
    specialize hGuniformcont 0.1
    have h0 : 0.1 > (0 : ℝ) := by norm_num
    apply hGuniformcont at h0
    rcases h0 with ⟨ε , hε1, hε2⟩
    have h1 : (0:E) ∈ (Metric.closedBall 0 1) := by simp
    have h2 := Set.mem_image_of_mem f h1
    apply hε2 (f 0) at h2
    have ⟨c, hc1, hc2⟩ : ∃ c, dist c (f 0) < ε ∧ c ∉ f '' Metric.closedBall 0 1 := by
      rw [mem_interior] at hnotinterior
      push_neg at hnotinterior
      specialize hnotinterior (Metric.ball (f 0) ε)
      simp only [Metric.isOpen_ball, Metric.mem_ball, dist_self,
      forall_const, imp_not_comm] at hnotinterior
      have hnotball := hnotinterior hε1
      rw [Set.not_subset] at hnotball
      rcases hnotball with ⟨c, hc1, hc2⟩
      exact ⟨c, ⟨Metric.mem_ball.mp hc1, (Set.mem_compl_iff (f '' Metric.closedBall 0 1) c).mp hc2⟩⟩
    let sigma1 : Set (E) := {y ∈ f '' (Metric.closedBall 0 1) | ‖y - c‖ ≥ ε}
    let sigma2 : Set (E) := Metric.sphere c ε
    let sigma := sigma1 ∪ sigma2
    -- change this proof to show that sigma1 and sigma2 are each compact as you use compactness of sigma1 later
    have hsigma1compact : IsCompact sigma1 := by
      rw [Metric.isCompact_iff_isClosed_bounded]
      refine ⟨?_, Bornology.IsBounded.subset (IsCompact.isBounded himgcompact) (Set.sep_subset (f '' Metric.closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)⟩
      have hsigma1eq : sigma1 = (f '' Metric.closedBall 0 1) ∩ {y | ‖y - c‖ ≥ ε } := by
        ext x
        exact ⟨fun hx ↦
            (Set.mem_inter_iff x (f '' Metric.closedBall 0 1) {y | ‖y - c‖ ≥ ε}).mpr
            hx, fun ⟨hx1, hx2⟩ ↦ ⟨(Set.mem_image f (Metric.closedBall 0 1) x).mpr hx1, le_of_eq_of_le rfl hx2⟩⟩
      have h4 : {y | ‖y - c‖ ≥ ε}ᶜ = Metric.ball c ε := by
            ext x
            constructor
            · intro hx
              rw [Set.mem_compl_iff, Set.notMem_setOf_iff, not_le] at hx
              exact mem_ball_iff_norm.mpr hx
            · intro hx
              simp only [ge_iff_le, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
              exact mem_ball_iff_norm.mp hx
      have h3 : IsOpen {y | ‖y - c‖ ≥ ε }ᶜ := by
          rw [h4]
          exact Metric.isOpen_ball
      exact IsClosed.and hballimageclosed ({ isOpen_compl := h3 })
    have hsigmacompact : IsCompact sigma := by
      apply IsCompact.union hsigma1compact
      rw [Metric.isCompact_iff_isClosed_bounded]
      exact ⟨ Metric.isClosed_sphere, Metric.isBounded_sphere⟩
    have hcnotinsigma : c ∉ sigma := by
      by_contra hcinsigma
      rw [Set.mem_union] at hcinsigma
      rcases hcinsigma with h1 | h2
      · rw [Set.mem_sep_iff] at h1
        rcases h1 with ⟨h1, h2⟩
        simp only [sub_self, norm_zero, ge_iff_le] at h2
        sorry
        -- aesop
      · have h3 : c ∈ Metric.sphere c ε := Metric.mem_sphere.mpr h2
        rw [mem_sphere_iff_norm] at h3
        simp at h3
        exact hε1.ne h3
    let Phi : (E) → (E) := fun y => c + (max (ε / ‖y - c‖) (1 : ℝ)) • (y - c)
    -- have hPhiimg : Phi '' (f '' Metric.closedBall 0 1) = sigma := by
    --     ext x
    have hPhicont : ContinuousOn Phi (f '' Metric.closedBall 0 1) := by
      -- fun_prop
      apply ContinuousOn.add continuousOn_const ?_


      apply ContinuousOn.smul ?_ ?_
      ·
        rw [continuousOn_iff_continuous_restrict]

        apply Continuous.max ((Continuous.div continuous_const (Continuous.norm (Continuous.sub continuous_subtype_val continuous_const))) ?_) continuous_const
        intro x
        simp only [ne_eq, norm_eq_zero]
        by_contra hx
        rw [sub_eq_zero] at hx
        subst hx
        simp_all only [ Subtype.coe_prop, not_true_eq_false]
      · apply ContinuousOn.sub (continuousOn_id' (f '' Metric.closedBall 0 1)) continuousOn_const

    have hGavoids : ∀ y ∈ sigma1, G y ≠ (0 : (E)) := by
      intro y hy
      by_contra hGeq
      -- have hGinjective : Function.Injective ((f '' Metric.closedBall 0 1).restrict G)  := by
      have hG_inj_on_image : Set.InjOn G (f '' Metric.closedBall 0 1) := by
        intro x hx y hy h
        have hx_eq : G x = hBn_inv_cmap ⟨x, hx⟩ := by
          rw [← ContinuousMap.restrict_apply G (f '' Metric.closedBall 0 1) ⟨x, hx⟩, hG]
        have hy_eq : G y = hBn_inv_cmap ⟨y, hy⟩ := by
          rw [← ContinuousMap.restrict_apply G (f '' Metric.closedBall 0 1) ⟨y, hy⟩, hG]
        rw [hx_eq, hy_eq] at h
        exact congr_arg Subtype.val (hBn_equiv.symm.injective h)
      have hyeq : y = f 0 := by
        have heq : G y = G (f 0) := SetCoe.ext (Eq.trans hGeq hG0.symm)
        apply hG_inj_on_image ((Set.mem_image f (Metric.closedBall 0 1) y).mpr hy.1) (Set.mem_image_of_mem f h1) at heq
        assumption
      rw [Set.mem_sep_iff, hyeq] at hy
      rw [dist_eq_norm, ← norm_neg, neg_sub] at hc1
      linarith
    let normG : E → ℝ := fun y => ‖(G y : E)‖
    -- have hgnormconton : ContinuousOn normG (f '' Metric.closedBall 0 1) := ContinuousOn.norm (continuous_subtype_val.comp_continuousOn hGconton)
    have hgnormconton1 : ContinuousOn normG sigma1 := ContinuousOn.norm (continuous_subtype_val.comp_continuousOn (ContinuousOn.mono hGconton (Set.sep_subset (f '' Metric.closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)))
    have hδ : ∃ (δ : ℝ), 0 < δ ∧ δ < 0.1 ∧ ∀ y ∈ sigma1, δ ≤ ‖(G y : E)‖ := by
      by_cases hP : sigma1.Nonempty
      · have ⟨z, hz, hmin⟩ := IsCompact.exists_isMinOn hsigma1compact hP hgnormconton1
        let δ := min (normG z) (0.05)
        have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨norm_pos_iff.mpr (hGavoids z hz), by norm_num⟩
        have hδ_lt_0_1 : δ < 0.1 := by
          calc δ ≤ 0.05 := min_le_right (normG z) 5e-2
          _ < 0.1 := by norm_num
        have hδ_lower : ∀ y ∈ sigma1, normG y ≥ δ := by
          intro y hy
          calc normG y ≥ normG z := hmin hy
            _ ≥ δ := min_le_left _ _
        use δ
      · exact ⟨0.05, ⟨by norm_num, ⟨by norm_num, fun y hy ↦ False.elim (hP ⟨y, hy⟩)⟩⟩⟩

    -- let b := Module.Basis.ofVectorSpace ℝ E
    let b := stdOrthonormalBasis ℝ E
    let n := Module.finrank ℝ E
    have h1  : 0 < n := (Module.finrank_pos_iff_of_free ℝ E).mpr hnontrivial
    have hn : n ≠ 0 := ne_zero_of_lt h1
    have hb := OrthonormalBasis.norm_eq_one b

    let coord_sigma (i : Fin n) : C(E, ℝ) :=
      { toFun := fun x => b.toBasis.equivFunL x i
        continuous_toFun := by fun_prop }
    have hcoord_diff (i : Fin n) : Differentiable ℝ (coord_sigma i) := by
      let proj_i : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
      exact (proj_i.comp (b.toBasis.equivFunL : E →L[ℝ] (Fin n → ℝ))).differentiable


    let generator_sigma : Set C(E, ℝ) := Set.range coord_sigma

    have hgen_diff : ∀ f ∈ generator_sigma, Differentiable ℝ f := by
      rintro _ ⟨i, rfl⟩
      exact hcoord_diff i

    let A_sigma : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ generator_sigma
    have hA_diff : ∀ f ∈ A_sigma, Differentiable ℝ f := by
      let D : Subalgebra ℝ C(E, ℝ) :=
        { carrier := {f | Differentiable ℝ f}
          zero_mem' := differentiable_const 0
          one_mem' := differentiable_const 1
          add_mem' := fun hf hg => hf.add hg
          mul_mem' := fun hf hg => hf.mul hg
          algebraMap_mem' := fun r => differentiable_const r }
      have : generator_sigma ⊆ D := hgen_diff
      have : A_sigma ≤ D := Algebra.adjoin_le this
      exact fun f hf => this hf

    have sep_sigma : A_sigma.SeparatesPoints := by
      intro x y hxy
      have hequiv: b.toBasis.equivFunL x ≠ b.toBasis.equivFunL y := by simpa
      obtain ⟨i, hi⟩ : ∃ i : (Fin n), b.toBasis.equivFunL x i ≠ b.toBasis.equivFunL y i := by
        contrapose! hequiv
        ext i
        exact (hequiv i)
      let f := coord_sigma i
      have hf_mem : f ∈ A_sigma := Algebra.subset_adjoin (Set.mem_range_self i)
      exact ⟨f, ⟨Set.mem_image_of_mem (fun f ↦ f.1) (hf_mem), hi⟩⟩
    let G_i (i : Fin n) : C(E, ℝ) :=
      { toFun := fun y => b.toBasis.equivFunL (G y) i,
        continuous_toFun := by
          fun_prop }
    let l := b.toBasis.equivFunL
    have hpos_symm : 0 < ‖(l.symm : ((Fin n) → ℝ) →L[ℝ] E)‖ := by
        refine lt_of_le_of_ne (norm_nonneg _) ?_
        intro h_eq
        have h_zero : (l.symm : (Fin n → ℝ) →L[ℝ] E) = 0 := norm_eq_zero.1 h_eq.symm
        let w : Fin n → ℝ := fun _ => 1
        have hw : w ≠ 0 := by
          haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h1
          rcases (show Nonempty (Fin n) by infer_instance) with ⟨i⟩
          intro h
          have : w i = 0 := congr_fun h i
          linarith
        have : (l.symm : (Fin n → ℝ) →L[ℝ] E) w = 0 := by rw [h_zero]; rfl
        have : l.symm w = 0 := this
        have : l (l.symm w) = l 0 := congrArg l this
        rw [l.apply_symm_apply w, map_zero] at this
        exact hw this
    let C := ‖(l.symm : (Fin n → ℝ) →L[ℝ] E)‖
    rcases hδ with ⟨δ, hδ1, hδ2⟩
    let ε' := δ / (2 * C)
    have hε' : 0 < ε' := by
      apply div_pos
      · exact RCLike.ofReal_pos.mp hδ1
      · apply mul_pos
        · exact zero_lt_two
        · exact hpos_symm
    have approx (i : Fin n) := ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints sep_sigma (G_i i) hsigmacompact hε'
    choose p_i hp_i using approx
    let P : C(E, E) :=
      { toFun := fun y => b.toBasis.equivFunL.symm (fun i => (p_i i : C(E, ℝ)) y),
        continuous_toFun := by fun_prop}
    have hP_bound : ∀ y ∈ sigma , ‖P y - G y‖ < δ := by
      intro y hy
      let v : Fin n → ℝ := fun i => (p_i i : C(E, ℝ)) y - (b.toBasis.equivFunL (G y)) i
      have hv i : |v i| < ε' := by
        have := (hp_i i).2 y hy
        sorry
        -- aesop
      have hnorm_v : ‖v‖ < ε' := by
        rw [pi_norm_lt_iff hε']
        intro i
        exact hv i
      have hP_eq : P y - G y = l.symm v := by
        dsimp [P, v]
        have h_repr_eq : b.toBasis.repr (G y) = l (G y) := rfl
        have hG : G y = l.symm (l (G y)) := (l.symm_apply_apply (G y)).symm
        have h_simp : l (l.symm (l (G y))) = l (G y) := by rw [l.symm_apply_apply (G y)]
        rw [h_repr_eq, hG, ← l.symm.map_sub, h_simp]
        rfl
      rw [hP_eq]
      have step2 : ‖l.symm v‖ ≤ ‖(l.symm : (Fin n → ℝ) →L[ℝ] E)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm_of_le (l.symm : (Fin n → ℝ) →L[ℝ] E) (le_refl ‖v‖)
      have step3 : ‖(l.symm : (Fin n → ℝ) →L[ℝ] E)‖ * ‖v‖ <
              ‖(l.symm : (Fin n → ℝ) →L[ℝ] E)‖ * ε' := mul_lt_mul_of_pos_left hnorm_v hpos_symm
      have step4 : ‖l.symm v‖ < ‖(l.symm : (Fin n → ℝ) →L[ℝ] E)‖ * ε' := lt_of_le_of_lt step2 step3
      calc
        ‖l.symm v‖ < C * ε' := step4
        _ = δ / 2 := by
          unfold ε'
          field_simp
          rw [div_self_eq_one₀]
          exact Ne.symm (ne_of_lt hpos_symm)
        _ < δ := half_lt_self hδ1
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    have h_sphere_null := MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume c (ne_of_gt hε1)

    have hp_i_diff (i : Fin n) : Differentiable ℝ (p_i i) := hA_diff (p_i i) (hp_i i).1
    have hP_diff : Differentiable ℝ P := by
      have h1 : Differentiable ℝ (fun y => fun i => (p_i i) y) := differentiable_pi.mpr hp_i_diff
      exact (l.symm : (Fin n → ℝ) →L[ℝ] E).differentiable.comp h1
    have hP_image_null : volume (P '' (Metric.sphere c ε)) = 0 := MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hP_diff.differentiableOn h_sphere_null


    have sigma1_subset_sigma : sigma1 ⊆ sigma := Set.subset_union_left

    have h0_notin_image : (0 : E) ∉ P '' sigma1 := by
      rintro ⟨y, hy, h⟩
      have hG : ‖(G y :E)‖ ≥ δ := (hδ2.2 y hy)
      have hP : ‖P y - G y‖ < δ := hP_bound y (sigma1_subset_sigma hy)

      rw [h] at hP
      have : ‖(G y : E)‖ = ‖G y - P y‖ := by rw [h, sub_zero]
      simp only [_root_.zero_sub, norm_neg] at hP
      linarith

    have ⟨v, hvnorm, hv1, hv2⟩ : ∃ (v: E), ‖v‖ < δ ∧ ¬ v ∈ P '' sigma1 ∧ ¬ v ∈ P '' sigma2:= by
      by_cases hsigma1nonempty : sigma1.Nonempty
      · have hP_cont : ContinuousOn (fun v => ‖P v‖) sigma1 := by fun_prop
        let ⟨d, hd1, hd2⟩ := IsCompact.exists_isMinOn hsigma1compact hsigma1nonempty hP_cont
        have hd3 : 0 < ‖P d‖ := by
          simp only [norm_pos_iff, ne_eq]
          by_contra heq0
          have : 0 ∈ P '' sigma1 := by
            rw [← heq0]
            exact Set.mem_image_of_mem (⇑P) hd1
          exact h0_notin_image this
        let k := min ‖P d‖ δ
        have hk : 0 < k := lt_min_iff.mpr ⟨hd3, hδ1⟩
        have hball_pos := Metric.measure_ball_pos volume (0 : E) hk
        have hnot_subset : ¬ (Metric.ball 0 k ⊆ P '' Metric.sphere c ε) := by
          intro hsub
          have : volume (Metric.ball (0 : E) k) ≤ volume (P '' Metric.sphere c ε) := measure_mono hsub
          rw [hP_image_null] at this
          have := lt_of_lt_of_le hball_pos this
          exact LT.lt.false this
        rw [Set.not_subset] at hnot_subset
        rcases hnot_subset with ⟨v, hvnorm, hv1⟩
        use v
        constructor
        · have hnormk : ‖v‖ < k := mem_ball_zero_iff.mp hvnorm
          have : k ≤ δ := min_le_right ‖P d‖ δ
          linarith
        · constructor
          · intro hin1
            rcases hin1 with ⟨x, hx, rfl⟩
            have : ‖P x‖ ≥ ‖P d‖ := by
              rw [isMinOn_iff] at hd2
              exact hd2 x hx
            have : ‖P x‖ < k := mem_ball_zero_iff.mp hvnorm
            have : k ≤ ‖P d‖ := min_le_left ‖P d‖ δ
            linarith
          · intro hin2
            exact hv1 hin2
      · have hball_pos := Metric.measure_ball_pos volume (0 : E) hδ1
        have hnot_subset2 : ¬ (Metric.ball 0 δ ⊆ P '' sigma2) := by
          intro hsub
          have : volume (Metric.ball (0 : E) δ) ≤ volume (P '' sigma2) := measure_mono hsub
          grind
        rcases Set.not_subset.1 hnot_subset2 with ⟨v, hv_in_ball, hv_notin_sigma2⟩
        use v
        constructor
        · exact mem_ball_zero_iff.mp hv_in_ball
        · constructor
          · intro h1
            exfalso
            rcases h1 with ⟨x, hx, rfl⟩
            exact hsigma1nonempty ⟨x, hx⟩
          · grind

    have h6: Continuous fun y => P y - v := by fun_prop

    let P' : C(E, E) :=
      { toFun := fun y => P y - v,
        continuous_toFun:= by fun_prop}

    let G_tilde : E → E := fun y => P' (Phi y)

    have hG_tilde_cont : ContinuousOn G_tilde (f '' Metric.closedBall 0 1):= by
      unfold G_tilde
      rw [continuousOn_iff_continuous_restrict]
      apply Continuous.comp ?_ ?_
      · exact ContinuousMap.continuous P'
      · exact ContinuousOn.restrict hPhicont


    specialize hStability_of_zero G_tilde hG_tilde_cont


    have h7 : ∀ y ∈ f '' (Metric.closedBall (0 : E) 1), ‖G y - G_tilde y‖ ≤ 1:= by
      intro y hy
      by_cases hP :  ε < ‖y - c‖
      ·
        have hPhi : Phi y = y := by
          unfold Phi
          have hright : ε / ‖y - c‖ < 1 := by
            have hyc : 0 < ‖y - c‖ := by linarith
            rwa [div_lt_one hyc]
          rw [max_eq_right_of_lt hright]
          simp
        unfold G_tilde
        rw [hPhi]

        have hy_sigma1 : y ∈ sigma1 := ⟨hy, le_of_lt hP⟩
        have hy_sigma : y ∈ sigma := Or.inl hy_sigma1


        calc
          ‖G y - P' y‖ = ‖G y - (P y - v)‖ := rfl
          _ = ‖(G y - P y) + v‖ := by rw [sub_sub_eq_add_sub, add_sub_right_comm]
          _ ≤ ‖G y - P y‖ + ‖v‖ := norm_add_le _ _
          _ = ‖P y - G y‖ + ‖v‖ := by rw [norm_sub_rev]
          _ ≤ δ + ‖v‖ := by grw [hP_bound y hy_sigma]
          _ = ‖v‖ + δ := add_comm _ _
          _ ≤ δ + δ := by grw [hvnorm]
          _ = 2 * δ := Eq.symm (two_mul δ)
          _ ≤ _ := by linarith
      ·
        simp only [not_lt] at hP
        unfold G_tilde
        have hy_neq_c : c ≠ y := by sorry
        have hpos : 0 < ‖y - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c))
        have hleft : 1 ≤ ε / ‖y - c‖ := (one_le_div hpos).mpr hP

        have hPhi : Phi y = c + (ε / ‖y - c‖) • (y-c) := by
          unfold Phi
          rwa [max_eq_left]



        calc
          ‖G y - P' (Phi y)‖
            = ‖G y - (P (Phi y) - v)‖ := rfl
          _ ≤ ‖(G y - P (Phi y)) + v‖ := by rw [sub_sub_eq_add_sub, add_sub_right_comm]
          _ ≤ ‖G y - P (Phi y)‖ + ‖v‖ := norm_add_le _ _

          -- _ ≤ ‖(G y : E)‖ + ‖P (Phi y)‖ + ‖v‖ := add_le_add (norm_sub_le (G y : E) (P (Phi y))) (le_refl ‖v‖)




            -- apply abs_norm_sub_norm_le




        --   unfold Phi
        --   rw [max_eq_left _]

        -- rw [hPhi]
        -- dsimp [P']

        -- specialize hP_bound (ε • y)




        -- calc
        --   ‖↑(G y) - P' (ε • y)‖





        -- calc
          -- ‖G y - P' (Phi y)‖
          --   = ‖G y - (P (Phi y) - v)‖ := rfl
          -- _ = ‖(G y - P (Phi y)) + v‖ := by rw [sub_sub_eq_add_sub, add_sub_right_comm]
          -- _ ≤ ‖G y - P (Phi y)‖ + ‖v‖ := norm_add_le _ _
          -- _ ≤ ‖(G y :E)‖ + ‖P (Phi y)‖ + ‖v‖ := add_le_add (norm_sub_le (G y : E) (P (Phi y))) (le_refl ‖v‖)
          -- _ ≤ 0.1 + ‖P (Phi y)‖ + ‖v‖ := add_le_add_right (add_le_add_left (hG_norm y h_in_image) _) _


        -- unfold G_tilde



            -- have hyc : 0 < ‖y - c‖ := by linarith
            -- rwa [div_lt_one hyc]


          -- _ < δ + ‖v‖ := add_lt_add_right (hP_bound y hy_sigma) ‖v‖


          -- add_lt_add_left (hP_bound y hy_sigma) _
          -- _ < δ + δ := add_lt_add_left hv _
          -- _ = 2δ := by ring



            -- rw [div_lt_one (norm_pos_iff.mpr (ne_of_gt hP))]
            -- exact hP
            -- aesop
      -- sorry

    -- let G_tilde : C(E, E) := P'.comp Phi











theorem invariance_of_domain (f : E → E)
    (hf_cont : Continuous f) (hf_inj : Function.Injective f) : IsOpenMap f := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hxU, hfx⟩
  rw [Metric.isOpen_iff] at hU
  have hclosedball: ∀ x' ∈ U, ∃ ε' > 0, Metric.closedBall x' ε' ⊆ U:= by
    intro x' hx'
    specialize hU x'
    apply hU at hx'
    rcases hx' with ⟨ε, hε, hball⟩
    refine ⟨ε/2, half_pos hε, ?_⟩
    trans Metric.ball x' ε
    · exact Metric.closedBall_subset_ball (div_two_lt_of_pos hε)
    · exact hball
  specialize hclosedball x hxU
  rcases hclosedball with ⟨ε, hε , hclosedball⟩
  let g := fun (v : E) => ε • v + x
  have hg_cont : Continuous g := ((continuous_const_smul ε).add continuous_const : Continuous g)
  have hg_inj : Function.Injective g:= by
    intro v1 v2 himeq
    dsimp [g] at himeq
    simp only [add_left_inj] at himeq
    exact (smul_right_inj (by linarith)).mp himeq
  let e := f ∘ g
  have he_cont : Continuous e := Continuous.comp hf_cont hg_cont
  have he_inj : Function.Injective e := Function.Injective.comp hf_inj hg_inj
  have h_interior : e 0 ∈ interior (e '' (Metric.closedBall 0 1)) :=
    restated_IoD e he_cont he_inj
  have h_g_eq : g '' (Metric.closedBall 0 1) = Metric.closedBall x ε := by
    unfold g
    rw [Eq.symm (Set.image_image (fun v ↦ v + x) (fun v ↦ ε • v) (Metric.closedBall 0 1)),
      Set.image_smul, smul_unitClosedBall]
    simp only [Real.norm_eq_abs, Set.image_add_right, Metric.preimage_add_right_closedBall,
      sub_neg_eq_add, zero_add]
    rw [abs_of_pos hε]
  use interior (f '' U)
  refine ⟨interior_subset, isOpen_interior, ?_⟩
  unfold e at h_interior
  rw [Set.image_comp] at h_interior
  rw [h_g_eq] at h_interior
  unfold g at h_interior
  simp only [Function.comp_apply, smul_zero, zero_add] at h_interior
  rw [hfx] at h_interior
  grw [hclosedball] at h_interior
  exact h_interior
