
import Mathlib.Tactic
-- import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist


/-- Let f be a continuous function on the unit ball in Euclidean space ℝ^n,
then f has at least one fixed point -/

-- theorem brouwer_fixed_point (n : ℕ)
--         (f : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 →
--         Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
--         (hf : Continuous f) : ∃ x, f x = x := by sorry


-- theorem restated_IoD (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
--         (hf_cont : Continuous f) (hf_inj : Function.Injective f)
--         : f 0 ∈ interior (f '' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) := by sorry


-- theorem invariance_of_domain (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
--         (hf_cont : Continuous f) (hf_inj : Function.Injective f) : IsOpenMap f := by
--     intro U hU

theorem brouwer_fixed_point (n : ℕ) (f : Euclidean.closedBall ((0 : EuclideanSpace ℝ (Fin n))) 1 →
        Euclidean.closedBall 0 1) (hf : Continuous f) : ∃ x, f x = x := by sorry


-- theorem restated_IoD (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
--         (hf_cont : Continuous f) (hf_inj : Function.Injective f)
--         : f 0 ∈ interior (Euclidean.closedBall 0 1) := by sorry
lemma zero_mem_closed_ball (n : ℕ) :
        (0 : EuclideanSpace ℝ (Fin n)) ∈ Euclidean.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    apply Euclidean.ball_subset_closedBall
    exact Euclidean.mem_ball_self zero_lt_one


theorem restated_IoD (n : ℕ)
    (f : Euclidean.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → EuclideanSpace ℝ (Fin n))
    (hf_cont : Continuous f)
    (hf_inj : Function.Injective f) :
    f ⟨0, (zero_mem_closed_ball n)⟩ ∈ interior (Set.range f) := by sorry

theorem invariance_of_domain (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (hf_cont : Continuous f) (hf_inj : Function.Injective f) : IsOpenMap f := by
    intro U hU
    rw [isOpen_iff_ball_subset]
    intro y hy
    rcases hy with ⟨x, hxU, hfx⟩
    have h := isOpen_iff_ball_subset.mp hU
    specialize (h) x hxU
    rcases h with ⟨nbd, hnbd1, hnbd2⟩
    rw [Metric.mem_uniformity_dist] at hnbd1
    rcases hnbd1 with ⟨ε, hε1, hε2⟩
    let g := fun (v : EuclideanSpace ℝ (Fin n)) => f (x + ε • v)
    have hg_cont : Continuous g :=
        hf_cont.comp (continuous_const.add (continuous_const.smul continuous_id))
    have hg_inj : Function.Injective g := by
        intro v1 v2 h
        have H2 : ε • v1 = ε • v2 := by
            have H := hf_inj h
            rw [add_right_inj] at H
            exact hf_inj (hf_inj (congrArg f (congrArg f (H))))
        rw [← sub_eq_zero] at H2 ⊢
        rw [← smul_sub] at H2
        rcases smul_eq_zero.mp H2 with (hε | hsub)
        ·   exfalso
            exact (ne_of_lt hε1) (id (Eq.symm hε))
        · exact hsub

    -- have restated := restated_IoD n ⟨g, by sorry⟩

    sorry
