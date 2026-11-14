# Paper correspondence

Manuscript: *Silver rate is sharp for gradient descent: strongly convex case*,
Yechan Jeong and Youngjoon Hong. The manuscript is not included in this package.

SHA-256: `c9f4d77d738064cc6a69f44b9d8e72619577f4802a381672158c83eeac5c8ce8`.

The formal target is Theorem 1.1. The proof constructs actual finite-dimensional objective functions and trajectories; it does not replace the worst-case errors by a dynamic-programming surrogate. Intermediate lemmas have explicit numerical and structural premises. The proof of the final theorem discharges them.

| Paper statement or step | Lean declaration | File |
| --- | --- | --- |
| Objective class and the two relative errors | `Admissible`, `Instance`, `iterate`, `D`, `E` | [Problem.lean](StrongSilver/Problem.lean) |
| Equivalent strong-convexity formulation | `admissible_iff_paper_class` | [Basic.lean](StrongSilver/Basic.lean) |
| Lemma 3.1: split stability and gain | `split_stability`, `split_power_decrease_le` | [SplitLemma.lean](StrongSilver/SplitLemma.lean) |
| Lemma 3.2: predecessor existence | `exists_predecessor` | [Predecessor.lean](StrongSilver/Predecessor.lean) |
| Lemma 3.3: planar construction and size estimates | `eventually_planar_construction`; `PlanarBoundaryCertificate.trajectory_prefix_bounds` | [PlanarConstruction.lean](StrongSilver/PlanarConstruction.lean), [PlanarTrajectoryBounds.lean](StrongSilver/PlanarTrajectoryBounds.lean) |
| Lemma 3.4: scalar coordinate and exact signed trajectory | `exists_scalar_trajectory_certificate` | [ScalarConstruction.lean](StrongSilver/ScalarConstruction.lean) |
| Lemma 3.5: phase attachment, retained suffix, gate and height | `LocalPhaseCertificate.exists_phase_attachment` | [PhaseAttachment.lean](StrongSilver/PhaseAttachment.lean) |
| Lemma 3.6: two-cone connector with original arbitrary steps | `two_cone_attachment` | [TwoConeAttachment.lean](StrongSilver/TwoConeAttachment.lean) |
| Lemma 3.7: working-cut realization and local replacements | `eventually_working_cut_distance_bound`, `eventually_working_cut_replacement_bound` | [WorkingCutBound.lean](StrongSilver/WorkingCutBound.lean), [WorkingCutReplacementBound.lean](StrongSilver/WorkingCutReplacementBound.lean) |
| Lemma 3.8: initial-cut realization | `eventually_initial_cut_distance_bound` | [InitialCutBound.lean](StrongSilver/InitialCutBound.lean) |
| Lemma 3.9: first-threshold power lower bound | `exists_absolute_first_threshold_power` | [FirstThresholdPower.lean](StrongSilver/FirstThresholdPower.lean) |
| Total averaged power decrease, (3.35) | `CounterexampleSequence.eventually_averaged_power_drop` | [AveragedPowerDrop.lean](StrongSilver/AveragedPowerDrop.lean) |
| Section 4.2: integral log, excess and refinement budgets | `eventually_band_integral_estimates` | [BandIntegralEstimates.lean](StrongSilver/BandIntegralEstimates.lean) |
| Section 4.3: visibility, bad-node and absolute-jump budgets | `eventually_band_visibility_estimates`, `eventually_band_bad_weight_rate`, `eventually_band_absolute_gain_budget` | [BandVisibilityEstimates.lean](StrongSilver/BandVisibilityEstimates.lean), [BandBadWeightRate.lean](StrongSilver/BandBadWeightRate.lean), [BandAbsoluteGainBudget.lean](StrongSilver/BandAbsoluteGainBudget.lean) |
| Lemma 4.1: finite four-phase attachment | `FourPhase.finite_four_phase_attachment` | [FourPhaseFiniteLemma.lean](StrongSilver/FourPhaseFiniteLemma.lean) |
| Lemma 4.2: depth extension and its application to actual available pairs | `eventually_two_gap_extension`, `eventually_band_pair_extension` | [TwoGapExtension.lean](StrongSilver/TwoGapExtension.lean), [BandPairExtension.lean](StrongSilver/BandPairExtension.lean) |
| Proposition 4.3, (4.25): excluded-pair count | `eventually_band_availability_budget` | [BandAvailabilityBudget.lean](StrongSilver/BandAvailabilityBudget.lean) |
| Proposition 4.3, (4.26): available-pair gain | `eventually_band_available_gain` | [BandPairGainBudget.lean](StrongSilver/BandPairGainBudget.lean) |
| Section 4.6: original-occurrence silver kernel and normalization | `eventually_band_kernel_representation`, `silverKernel_integral`, `eventually_band_normalized_kernel_budget` | [BandKernelRepresentation.lean](StrongSilver/BandKernelRepresentation.lean), [SilverKernelIntegral.lean](StrongSilver/SilverKernelIntegral.lean), [BandNormalizedKernelBudget.lean](StrongSilver/BandNormalizedKernelBudget.lean) |
| Exact original-threshold averaging and pad conversion | `averaged_original_power_jumps`, `eventually_band_gamma_to_jumps` | [OriginalLogPowerAverage.lean](StrongSilver/OriginalLogPowerAverage.lean), [BandWeightedJumpSupport.lean](StrongSilver/BandWeightedJumpSupport.lean) |
| Band estimate (4.1) | `eventually_band_power_decrease_upper` | [BandPowerDecreaseUpper.lean](StrongSilver/BandPowerDecreaseUpper.lean) |
| All band premises on the same schedule and curvature | `CounterexampleSequence.eventually_uniform_band_source` | [CounterexampleBandSource.lean](StrongSilver/CounterexampleBandSource.lean) |
| Section 5.1: uniform finite-ladder summation | `geometric_band_rate_sum`, `geometric_band_rate_tail_tendsto_zero`; `CounterexampleSequence.eventually_total_band_power_upper` | [GeometricBandRateSum.lean](StrongSilver/GeometricBandRateSum.lean), [CounterexampleBandPower.lean](StrongSilver/CounterexampleBandPower.lean) |
| Section 5.1: contradiction and weighted-count bound | `no_counterexample_sequence`, `weighted_count_bound`, `exists_weighted_count_bound` | [WeightedCountBound.lean](StrongSilver/WeightedCountBound.lean) |
| Section 5.2: distance bound and repetition for value error | `main_lower_bound_of_weighted_count_bound`; `value_lower_of_repetitions`, `main_iff_distance_lower` | [TargetReduction.lean](StrongSilver/TargetReduction.lean), [RepetitionBridge.lean](StrongSilver/RepetitionBridge.lean) |
| Theorem 1.1 | `silver_rate_lower_bound_explicit`, `silver_rate_lower_bound_horizon` | [Main.lean](StrongSilver/Main.lean) |

The intermediate formulations use explicit finite numerical bounds in place of asymptotic notation. The map identifies the versions used in the formal proof, rather than asserting literal equality of every displayed intermediate constant or auxiliary parameter range in the PDF.

The planar boundary uses the smooth slope `k0*cos(theta)/(cos(theta)+2*k0*sin(theta))` in place of a nonsmooth minimum. Its required bounds, boundary equation, convex body, predecessor trajectories and projection properties are proved in the package.

In the right ordinary suffix for Lemma 4.2, the formal proof uses the proved offset bound `A^(-1/20)`, in place of the intermediate `O(A^(-.10))` estimate in the PDF. The weaker bound still supplies the full two-gap improvement and the final band estimate. It is discharged in [OrdinaryRootSuffix.lean](StrongSilver/OrdinaryRootSuffix.lean) and the subsequent finite construction.

The finite two-gap construction uses `mu*B <= 1/10000`. This is proved for the final counterexample argument by choosing an absolute cap `a <= 1/1000000`; [InitialCapArbitrarilySmall.lean](StrongSilver/InitialCapArbitrarilySmall.lean) supplies such a cap while preserving the initial power lower bound. No assumption that `mu*B` tends to zero is made.

Reservations need not be measurable as functions of the cutoff. The proof combines the pointwise available-pair and excluded-gap bounds into explicit integrable source envelopes before integrating. The final band bound is

$$
\Gamma(u,u/r)\le K W\bigl[(\log u)^{-3}+u^{-1/1000}\bigr].
$$

Both terms are summable on the actual finite geometric ladder, with a tail bound tending to zero. This contradicts the lower bound by a positive absolute multiple of the same `W`. The final theorem has no remaining weighted-count or band-estimate premise.
