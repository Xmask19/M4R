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
-- import Mathlib.MeasureTheory.MeasureSpace
-- import Mathlib.MeasureTheory.Constructions.PiLp
variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open NNReal
open MeasureTheory MeasureTheory.Measure

-- theorem stoneweierstrass {X : Type u_1} [TopologicalSpace X] [CompactSpace X] (A : Subalgebra E C(X, E)) (w : A.SeparatesPoints) (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) :
--         ∃ (g : ↥A), ‖↑g - f‖ < ε := by sorry
-- #synth MeasureSpace (EuclideanSpace ℝ (Fin 3))

set_option linter.unnecessarySimpa false
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
      (hGtilde : Continuous Gtilde) (hy : ∀ y ∈ (f '' (Metric.closedBall 0 1)), ‖G y - Gtilde y‖ ≤ 1 ) : ∃ y ∈ f '' (Metric.closedBall 0 1), Gtilde y = 0 := by
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
    have diff_fun_cont_on : ContinuousOn diff_fun (Metric.closedBall 0 1):=
      ContinuousOn.sub (continuousOn_id' (Metric.closedBall 0 1)) (Continuous.comp_continuousOn' hGtilde hf_cont)
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
        aesop
      · have h3 : c ∈ Metric.sphere c ε := Metric.mem_sphere.mpr h2
        rw [mem_sphere_iff_norm] at h3
        simp only [sub_self, norm_zero] at h3
        aesop
    let Phi : (E) → (E) := fun y => (max (ε / ‖y - c‖) (1 : ℝ)) • y
    -- have hPhiimg : Phi '' (f '' Metric.closedBall 0 1) = sigma := by
    --     ext x
    have hPhicont : ContinuousOn Phi (f '' Metric.closedBall 0 1) := by
      apply ContinuousOn.smul ?_ (continuousOn_id' (f '' Metric.closedBall 0 1))
      rw [continuousOn_iff_continuous_restrict]
      apply Continuous.max ((Continuous.div continuous_const (Continuous.norm (Continuous.sub continuous_subtype_val continuous_const))) ?_) continuous_const
      intro x
      simp only [ne_eq, norm_eq_zero]
      by_contra hx
      rw [sub_eq_zero] at hx
      aesop
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
    -- have : Fintype ι := by sorry

    -- let coord (i : ι): C(E, ℝ) :=
    --   { toFun := fun x => b.equivFunL x i,
    --     continuous_toFun := by fun_prop }

    -- -- let coord_E (i : ι) : C(E, ℝ) :=
    -- --     { toFun := fun y => l y i,
    -- --         continuous_toFun := (continuous_apply i).comp l.continuous }
    -- let generator_E : Set C(E, ℝ) := Set.range coord
    -- let A_E : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ generator_E

    let coord_sigma (i : Fin n) : C(sigma, ℝ) :=
      { toFun := fun x => b.toBasis.equivFunL x i
        continuous_toFun := by fun_prop }

    let generator_sigma : Set C(sigma, ℝ) := Set.range coord_sigma
    let A_sigma : Subalgebra ℝ C(sigma, ℝ) := Algebra.adjoin ℝ generator_sigma

    have sep_sigma : A_sigma.SeparatesPoints := by
      intro x y hxy
      have hxy' : (x : E) ≠ (y : E) :=
        Subtype.coe_ne_coe.mpr hxy
      have hequiv: b.toBasis.equivFunL x ≠ b.toBasis.equivFunL y := by simpa
      obtain ⟨i, hi⟩ : ∃ i : (Fin n), b.toBasis.equivFunL x i ≠ b.toBasis.equivFunL y i := by
        contrapose! hequiv
        ext i
        exact (hequiv i)
      let f := coord_sigma i
      have hf_mem : f ∈ A_sigma := Algebra.subset_adjoin (Set.mem_range_self i)
      exact ⟨f, ⟨Set.mem_image_of_mem (fun f ↦ f.1) (hf_mem), hi⟩⟩


    let incl : C(Metric.closedBall (0 : E) 1, E) := ⟨Subtype.val, continuous_subtype_val⟩
    let G_rest : C(sigma, E) := incl.comp (G.restrict sigma)
    let G_i (i : Fin n) : C(sigma, ℝ) :=
      { toFun := fun y => b.toBasis.equivFunL (G_rest y) i,
        continuous_toFun := by
          fun_prop }
    haveI : CompactSpace sigma := isCompact_iff_compactSpace.mp hsigmacompact


    -- have h_card_ne_zero : Fintype.card (Fin n) ≠ 0 := Ne.symm (Ne.intro fun a ↦ hdim_zero (Eq.symm a))
    -- have n_ne_zero : n ≠ 0 := by rwa [Fintype.card_fin n] at h_card_ne_zero
    -- have n_pos : 0 < n := Nat.pos_of_ne_zero n_ne_zero
    -- have : (n : ℝ) ≠ 0 := by exact_mod_cast n_ne_zero

    -- let norm_l := ‖(l : E →L[ℝ] (ι → ℝ))‖
    -- let norm_l_symm := ‖(l.symm : (ι → ℝ) →L[ℝ] E)‖
    -- let C := (max norm_l norm_l_symm) + 1
    -- have hC : 0 < C := by positivity
    rcases hδ with ⟨δ, hδ1, hδ2⟩
    let ε' := δ / n
    have hd : 0 ≤ n := Nat.zero_le n
    have hε' : 0 < ε' := by
      apply div_pos
      · exact RCLike.ofReal_pos.mp hδ1
      · apply lt_iff_le_and_ne.mpr
        refine ⟨Nat.cast_nonneg' n, ?_⟩
        rw [← Nat.cast_ne_zero (R := ℝ )] at hn
        exact hn.symm

    -- div_pos hδ1 (mul_pos  (lt_of_le_of_ne hd (Ne.symm hdim_zero)))
    have approx (i : (Fin n)) : ∃ p_i : A_sigma, ‖(p_i : C(sigma, ℝ)) - G_i i‖ < ε' :=
      ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
        A_sigma sep_sigma (G_i i) ε' hε'
    choose p_i hp_i using approx


    let P : C(sigma, E) :=
      { toFun := fun y => b.toBasis.equivFunL.symm (fun i => (p_i i : C(sigma, ℝ)) y),
        continuous_toFun := by fun_prop}

    have hP_bound : ∀ y , ‖P y - G_rest y‖ < δ := by
      intro y

      let v : Fin n → ℝ := fun i => (p_i i : C(sigma, ℝ)) y - (b.toBasis.equivFunL (G_rest y)) i
      have hv i : |v i| < ε' := by
        have := hp_i i
        rw [ContinuousMap.norm_lt_iff _ hε'] at this
        exact this y

      let l := b.toBasis.equivFunL


      have hP_eq : P y - G_rest y = l.symm v := by
        dsimp [P, v]
        have h_repr_eq : b.toBasis.repr (G_rest y) = l (G_rest y) := rfl
        have hG : G_rest y = l.symm (l (G_rest y)) := (l.symm_apply_apply (G_rest y)).symm
        have h_simp : l (l.symm (l (G_rest y))) = l (G_rest y) := by rw [l.symm_apply_apply (G_rest y)]
        rw [h_repr_eq, hG, ← l.symm.map_sub, h_simp]

        rfl


      rw [hP_eq]
      -- rw?


      -- have hG : G_rest y = l.symm (l (G_rest y)) := (l.symm_apply_apply (G_rest y)).symm
      -- rw [hG]
        -- rw [← b.toBasis.equivFunL.symm.map_sub]
        -- congr

      -- have hnorm_v : ‖v‖ ^ 2 = ∑ i, (v i) ^ 2 := by rw [EuclideanSpace.norm_sq_eq_sum]

      -- have hnorm : ‖P y - G_rest y‖ ^ 2 = ∑ i, (v i) ^ 2 := by
      --   rw [← b.toBasis.equivFunL.norm_map, ← b.toBasis.equivFunL.map_sub]
      --   rw [EuclideanSpace.norm_sq_eq_sum]

      -- have hnorm : ‖P y - G_rest y‖ ^ 2 =  (∑ i, ((p_i i : C(sigma, ℝ)) y - (b.toBasis.equivFunL (G_rest y)) i)^2) := by
      --   rw [EuclideanSpace.norm_sq_eq]
      --   apply congr_arg (Finset.sum Finset.univ)
      --   funext i
      --   have : (P y - G_rest y).ofLp i = (P y).ofLp i - (G_rest y).ofLp i := by rfl
      --   rw [this]
      --   simp only [Real.norm_eq_abs, sq_abs]
      --   have hcoor : (P y).ofLp i = (p_i i : C(sigma1, ℝ)) y := by dsimp [P]
      --   rw [hcoor]

      have hsq (i : Fin n) : (v i)^2 < ε'^2 := by
        rw [sq_lt_sq, abs_of_pos hε']
        exact RCLike.ofReal_lt_ofReal.mp (hv i)
      have h_eq : Fintype.card (Fin n) = n := Fintype.card_fin n

      haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h1
      have univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
      have hsum : ∑ i, v i ^ 2 < ∑ (i : Fin n), ε' ^ 2 := by

        apply Finset.sum_lt_sum_of_nonempty univ_nonempty
        intro i _
        exact hsq i

      have hRHS : Finset.sum (Finset.univ : Finset (Fin n)) (fun _ => ε' ^ 2) = n * ε' ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ]
        simp


      have hpos_symm : 0 < ‖l.symm‖ := by
        refine lt_of_le_of_ne (norm_nonneg _) ?_
        intro h_eq  -- assume ‖l.symm‖ = 0
        have h_zero : l.symm = 0 := norm_eq_zero.1 h_eq
        -- Choose a non‑zero vector in the domain, e.g., the constant 1 function
        let w : ι → ℝ := fun _ => 1
        have hw : w ≠ 0 := by simp
        have : l.symm w = 0 := by rw [h_zero, ContinuousLinearMap.zero_apply]
        -- Apply l to both sides
        have : l (l.symm w) = 0 := congrArg l this
        rw [l.apply_symm_apply w] at this
        exact hw this  -- contradiction: w = 0


      have hnorm_v : ‖v‖ < ε' := by
        rw [pi_norm_lt_iff hε']
        intro i
        exact hv i


      -- let ε'nn : ℝ≥0 := ⟨ε', le_of_lt hε'⟩
      -- have hnorm_v : ‖v‖ < ε' := by
      --   rw [Pi.norm_def]  -- ‖v‖ = (Finset.univ.sup fun i ↦ ‖v i‖₊).toReal
      --   rw [← NNReal.coe_lt_coe]  -- turn (toReal ... < ε') into (sup < ε'nn)
      --   apply Finset.sup_lt_iff
      --   · exact univ_nonempty
      --   · intro i _
      --     have := hv i
      --     rwa [← NNReal.coe_lt_coe] at this


      -- have hnorm_v : ‖v‖ < ε' := by
      --   rw [Pi.norm_def]
      --   apply Finset.sup_lt_iff (Finset.univ_nonempty)
      --   intro i _
      --   exact hv i

      -- have hnorm : ‖l.symm v‖ ≤ ‖l.symm‖ * ‖v‖_sup := ContinuousLinearMap.le_op_norm _ _

      -- rw [pi_norm_lt_iff hδ1]

      -- have hsup : ‖v‖ < ε' := by
      --   rw [Pi.norm_def]
      --   apply Finset.sup_lt_iff (Finset.univ_nonempty)
      --   intro i _
      --   exact hv i
      -- have hnorm_v : ‖v‖ < Real.sqrt n * ε' := by
      --   rw [EuclideanSpace.norm_eq]
      --   rw [← Real.sqrt_lt_sqrt_iff (norm_nonneg _) (by positivity)]
      --   rw [Real.sqrt_mul (le_of_lt (by positivity)) (sq_nonneg ε')]
      --   exact hsum

      -- rw [hnorm] at hsum

    -- have hspherevolume : volume (Metric.sphere c ε) = 0 := addHaar_sphere_of_ne_zero volume c (ne_of_gt hε1)


      -- let n : ℝ := Fintype.card (Fin n)
      -- have hRHS : ∑ i in Finset.univ, ε' ^ 2 = n * ε' ^ 2 := by
      -- rw [Finset.sum_const, Finset.card_univ, Nat.cast_inj]

      -- have n_pos : 0 < n := Nat.pos_of_ne_zero h_card_ne_zero
      -- haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp h_card_ne_zero


        -- intro h_card_zero
        -- have hd_zero : d = 0 := calc
        --     d = ↑(Fintype.card (Fin n)) := rfl
        --     _ = ↑0 := by rw [h_card_zero]
        --     _ = 0 := Nat.cast_zero
        -- exact hdim_zero hd_zero

      -- have h_card_ne_zero : Fintype.card (Fin n) ≠ 0 := by
      --     intro h_card_zero
      --     have : d = 0 := by rw [d, h_card_zero, Nat.cast_zero]
      --     exact hdim_zero this
        -- have h : n = 0 := Nat.eq_zero_of_not_pos hdim_zero  -- careful: hdim_zero is ¬d=0
        -- rw [d, h, Nat.cast_zero]

      -- haveI : Nonempty (Fin n) := by
      --     -- Prove that n ≠ 0 (this should be from your context, e.g., because you have already handled the zero‑dimensional case separately)
      --     have hn_pos : 0 < n := by

      -- have univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
      -- have hsum : ∑ i in Finset.univ, (v i)^2 < ∑ i in Finset.univ, ε'^2 :=
      -- Finset.sum_lt_sum_of_nonempty univ_nonempty (fun i _ => hsq i)
        -- apply?

        -- exact ⟨abs_nonneg (v i), hv i⟩



      -- have hsq (i : Fin n) : ((p_i i : C(sigma1, ℝ)) y - (G_rest y).ofLp i)^2 < ε'^2 := by
      --     have h := hv i y   -- hv i : |...| < ε'
      --     rw [← sq_abs]
      --     exact pow_lt_pow_left (abs_lt.mp h).1 (norm_nonneg _) two_pos

      -- have hsum :

      -- have hsum : ∑ i in Finset.univ, ((p_i i : C(sigma1, ℝ)) y - (G_rest y).ofLp i)^2 < ∑ i, ε'^2 := by
      --     refine Finset.sum_lt_sum (fun i _ => sq_nonneg _) (fun i _ => ?_)

        -- simp?
        -- rw [sq_abs]

        -- refine Finset.sum_congr rfl fun i _ => ?_
        -- rw [Pi.sub_apply]
        -- simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]


      --     rw [EuclideanSpace.norm_eq]
      --     simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
      --     congr
        -- simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
        -- have h1 : (∑ x, ((P y).ofLp x - (G_rest y).ofLp x) ^ 2)
        -- refine Finset.sum_congr rfl fun i _ => ?_

        -- apply congr_arg (Finset.sum Finset.univ)
        -- refine Finset.sum_congr rfl (fun i _ => ?_)
        -- congr
        -- ext i
        -- -- congr
    --     intro y
    --     let dvec : ι → ℝ := fun i => (p_i i : C(sigma1, ℝ)) y - (l (G_rest y)) i

    --     haveI : Nonempty ι := not_isEmpty_iff.1 $ λ h_isEmpty => hdim_zero $ (Nat.cast_eq_zero (R := ℝ)).mpr $ Fintype.card_eq_zero_iff.2 h_isEmpty
    --     have univ_nonempty : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty

    --     have h_coord (i : ι) : |dvec i| < ε' := by
    --         have := hp_i i
    --         rw [ContinuousMap.norm_lt_iff _ hε'] at this
    --         exact this y

    --     let ε'nn : ℝ≥0 := ⟨ε', le_of_lt hε'⟩
    --     have h_coord_nn i : ‖dvec i‖₊ < ε'nn := by
    --         rw [← NNReal.coe_lt_coe]
    --         exact h_coord i

    --     have h_sup : (Finset.univ.sup fun i => ‖dvec i‖₊) < ε'nn := by
    --         rw [Finset.sup_lt_iff]
    --         · intro i _
    --             exact h_coord_nn i
    --         · exact coe_lt_coe.mp hε'

    --     have h_norm_eq : ‖dvec‖ = (Finset.univ.sup fun i => ‖dvec i‖₊).toReal := by rw [Pi.norm_def]
    --     have h_norm_dvec : ‖dvec‖ < ε' := by
    --         rw [h_norm_eq]
    --         exact gt_iff_lt.mp h_sup

    --     have h_eq : P y - G_rest y = l.symm dvec := by
    --         dsimp [P]
    --         have h : G_rest y = l.symm (l (G_rest y)) := (l.symm_apply_apply (G_rest y)).symm
    --         rw [h]
    --         rw [← l.symm.map_sub]
    --         rfl


    --     have h_pos_norm : 0 < norm_l_symm := by
    --         refine lt_of_le_of_ne (norm_nonneg _) ?_
    --         intro h_eq

    --         have h_l_symm_zero : (l.symm : (ι → ℝ) →L[ℝ] E) = 0 := by
    --             rw [norm_l_symm] at h_eq
    --             exact (norm_eq_zero.mp h_eq)
        -- simp [norm_l_symm] at h_eq
        -- have h_l_symm_zero : (l.symm : (ι → ℝ) →L[ℝ] E) = 0 := (norm_eq_zero.1 h_eq)
        -- have h_pointwise : ∀ x, l.symm x = 0 := by
        --     intro x
        --     exact (ContinuousLinearMap.ext_iff (f := l.symm) (g := 0)).mp h_l_symm_zero x



        -- have h_l_symm_zero : (l.symm : (ι → ℝ) →L[ℝ] E) = 0 := (norm_eq_zero.1 h_eq.symm)


        -- have h_comp : (l : E →L[ℝ] (ι → ℝ)) ∘L (l.symm : (ι → ℝ) →L[ℝ] E) = ContinuousLinearMap.id ℝ (ι → ℝ) :=
        --     ContinuousLinearEquiv.self_comp_symm l
        -- have : ContinuousLinearMap.id ℝ (ι → ℝ) = (l : E →L[ℝ] (ι → ℝ)) ∘L (l.symm : (ι → ℝ) →L[ℝ] E) :=
        --         by rw [← ContinuousLinearEquiv.coe_comp_coe_symm]; rfl

        -- refine ⟨fun i _ => h_coord_nn i, fun heq => ?_⟩
        -- exact ⟨univ_nonempty, fun i _ => h_coord_nn i⟩
      -- have h_sup : (Finset.univ.sup fun i => ‖dvec i‖₊) < ε'nn := by
      --     apply (Finset.sup_lt_iff univ_nonempty).mpr
      --     intro i _
      --     exact h_coord_nn i

      -- have h_sup : (Finset.univ.sup fun i => ‖dvec i‖₊) < ε'nn := by
      --     rw [Finset.sup_lt_iff]
      --     ·
      --     ·
        -- constructor
        -- apply Finset.sup_lt_iff
        -- · exact univ_nonempty
        -- · intro i _
        --     exact h_coord_nn i


      -- let sup_norm := Finset.univ.sup' univ_nonempty (fun i => |dvec i|)
      -- have hsup : sup_norm < ε' := (Finset.sup'_lt_iff univ_nonempty).mpr (fun i _ => h_coord i)
      -- have hnorm_eq : ‖dvec‖ = sup_norm := by
      --     rw [Pi.norm_def, sup_norm]



      -- have hsup_real : Finset.univ.max' (fun i => ‖dvec i‖) (Finset.univ_nonempty) < ε' := by
      --     apply Finset.max_lt
      --     intro i _
      --     exact hd i  -- hd i : |dvec i| < ε', and note that |dvec i| = ‖dvec i‖

      -- let ε'_nn : ℝ≥0 := ⟨ε', le_of_lt hε'⟩
      -- have hd i : |dvec i| < ε' := by
      --     have := hp_i i
      --     rw [ContinuousMap.norm_lt_iff _ hε'] at this
      --     exact this y
      -- have hsup : Finset.univ.sup (fun i => ‖dvec i‖₊) < ε'nn := by
      --     apply Finset.sup_lt_iff
      --     · exact Finset.univ.nonempty
      --     · intro i _
      --         exact hd_nn i


      -- have hsup : ‖dvec‖ < ε' := by
      --     rw [Pi.norm_def]
      --     let ε'nn : ℝ≥0 := ⟨ε', hε'.le⟩
        -- apply Finset.sup_lt_iff (by linarith [hε'])
        -- intro i _
        -- exact hd i
    --     have h1 : ‖P y - G_rest y‖^2 = ∑ i, ((p_i i : C(sigma1, ℝ)) y - (l (G_rest y)) i)^2 := by




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
