import MasterEquation


-- Theorem 1 (Master Equation jump)
#print axioms MasterEquation.lnew_isGreatest
#print axioms MasterEquation.dust_nonneg
#print axioms MasterEquation.dustX_eq_zero_iff
#print axioms MasterEquation.dustY_eq_zero_iff
#print axioms MasterEquation.dust_mul_eq_zero
#print axioms MasterEquation.dust_both_zero_iff
#print axioms MasterEquation.exactly_one_dust_zero
#print axioms MasterEquation.slack_leftover_of_token0_binds
#print axioms MasterEquation.dust_add_eq_abs_sub
#print axioms MasterEquation.dust_of_proportional_requirements
#print axioms MasterEquation.lp_below_range
#print axioms MasterEquation.lp_above_range
#print axioms MasterEquation.lnew_gs_corner

-- Proposition 1 (binding-side criterion), Corollary 1 (swap-free rule), Corollary 2 (swap-corrected rule)
#print axioms MasterEquation.token1_binds_iff
#print axioms MasterEquation.token0_leaks
#print axioms MasterEquation.token1_leaks
#print axioms MasterEquation.slack_leftover_of_token1_binds
#print axioms MasterEquation.shareRequired_mem
#print axioms MasterEquation.share_sub
#print axioms MasterEquation.share_lt_iff
#print axioms MasterEquation.share_gt_iff
#print axioms MasterEquation.share_eq_iff
#print axioms MasterEquation.criterion_leftover_token1
#print axioms MasterEquation.criterion_leftover_token0
#print axioms MasterEquation.criterion_no_leftover
#print axioms MasterEquation.centred_requirements
#print axioms MasterEquation.shareRequired_centred
#print axioms MasterEquation.withdrawn_mismatch
#print axioms MasterEquation.withdrawn_value
#print axioms MasterEquation.alpha_den_pos
#print axioms MasterEquation.alpha_nonneg
#print axioms MasterEquation.alpha_eq_sinh
#print axioms MasterEquation.mismatch_eq_alpha_value_up
#print axioms MasterEquation.mismatch_eq_alpha_value_down
#print axioms MasterEquation.dust_centred
#print axioms MasterEquation.dustX_eq_zero_of_value
#print axioms MasterEquation.swapfree_surplus_token1
#print axioms MasterEquation.swapfree_surplus_token0
#print axioms MasterEquation.balance_below_surplus_keeps_token1
#print axioms MasterEquation.balance_below_surplus_keeps_token0
#print axioms MasterEquation.balance_equal_surplus_removes_token1
#print axioms MasterEquation.balance_equal_surplus_removes_token0
#print axioms MasterEquation.balance_above_surplus_reverses_token1
#print axioms MasterEquation.balance_above_surplus_reverses_token0
#print axioms MasterEquation.swapcorrected_surplus_token1
#print axioms MasterEquation.swapcorrected_surplus_token0
#print axioms MasterEquation.swap_feasible_token1
#print axioms MasterEquation.swap_feasible_token0
#print axioms MasterEquation.swapfree_rule_up
#print axioms MasterEquation.swapfree_rule_down
#print axioms MasterEquation.swapfree_rule_exit_above
#print axioms MasterEquation.swapfree_rule_exit_below
#print axioms MasterEquation.swapfree_rule_up_with_balance
#print axioms MasterEquation.swapfree_rule_down_with_balance
#print axioms MasterEquation.swapcorrected_rule_up
#print axioms MasterEquation.swapcorrected_rule_down
#print axioms MasterEquation.swapcorrected_leftover_value

-- Theorem 2 (multi-pool mass conservation without a swap)
#print axioms MasterEquation.Rebalance.mass_conservation
#print axioms MasterEquation.Rebalance.value_conservation
#print axioms MasterEquation.impacts_add_ledger_change_eq_zero
#print axioms MasterEquation.mixed_sign_of_sum_zero

-- Lemma 1 (transfers sum to zero)
#print axioms MasterEquation.Transfers.transfer_nonneg
#print axioms MasterEquation.Transfers.sum_eq_others_add
#print axioms MasterEquation.Transfers.transfer_le_others
#print axioms MasterEquation.Transfers.sum_netTransfer_others
#print axioms MasterEquation.Transfers.sum_netTransfer_eq_zero
#print axioms MasterEquation.Transfers.sum_entitlementAfter
#print axioms MasterEquation.Transfers.entitlementAfter_nonneg
#print axioms MasterEquation.Transfers.transfer_eq_zero_of_alone
#print axioms MasterEquation.Transfers.others_eq_zero_of_subsingleton
#print axioms MasterEquation.Transfers.value_change
#print axioms MasterEquation.Transfers.sum_cumulative_eq_zero
#print axioms MasterEquation.Transfers.receiver_and_giver

-- The direction-resolved hub-spoke kernel: derivation, l1 identity, invariant set, side identity, contraction for one mark, one register, position size (Lemma 2, Propositions 2 and 3, and Proposition S1 of the supplement, deterministic parts)
#print axioms MasterEquation.Kernel.inputs_up
#print axioms MasterEquation.Kernel.inputs_down
#print axioms MasterEquation.Kernel.hat_diff
#print axioms MasterEquation.Kernel.kernel_eq_master_jump
#print axioms MasterEquation.Kernel.hubPost_eq_ite
#print axioms MasterEquation.Kernel.spokePost_eq_ite
#print axioms MasterEquation.Kernel.hubPost_nonneg
#print axioms MasterEquation.Kernel.spokePost_nonneg
#print axioms MasterEquation.Kernel.post_mul_eq_zero
#print axioms MasterEquation.Kernel.leftover_magnitude
#print axioms MasterEquation.Kernel.abs_pos_part_sub_add_abs_neg_part_sub
#print axioms MasterEquation.Kernel.l1_identity
#print axioms MasterEquation.Kernel.abs_imbalance_sub_le
#print axioms MasterEquation.Kernel.l1_contraction
#print axioms MasterEquation.Kernel.bstar_fixed
#print axioms MasterEquation.Kernel.bstar_nonneg
#print axioms MasterEquation.Kernel.bstar_lt
#print axioms MasterEquation.Kernel.imbalance_bounds
#print axioms MasterEquation.Kernel.imbalance_pos
#print axioms MasterEquation.Kernel.post_le_bstar
#print axioms MasterEquation.Kernel.spokePost_eq_zero_iff
#print axioms MasterEquation.Kernel.hubPost_eq_zero_iff
#print axioms MasterEquation.Kernel.hubPost_eq_affine
#print axioms MasterEquation.Kernel.spokePost_eq_affine
#print axioms MasterEquation.Kernel.spokePost_slack
#print axioms MasterEquation.Kernel.slack_side_bound
#print axioms MasterEquation.Kernel.step_hub
#print axioms MasterEquation.Kernel.step_spoke
#print axioms MasterEquation.Kernel.step_other
#print axioms MasterEquation.Kernel.step_l1_contraction
#print axioms MasterEquation.Kernel.step_l1_contraction_sum
#print axioms MasterEquation.Kernel.step_eq_theta
#print axioms MasterEquation.Kernel.one_register_step
#print axioms MasterEquation.Kernel.one_register
#print axioms MasterEquation.Kernel.sq_post
#print axioms MasterEquation.Kernel.imbalance_sq_le
#print axioms MasterEquation.Kernel.sq_drift_pointwise
#print axioms MasterEquation.Kernel.sq_drift_integral
#print axioms MasterEquation.Kernel.new_liquidity_value
#print axioms MasterEquation.Kernel.size_conservation
#print axioms MasterEquation.Kernel.own_value_change
#print axioms MasterEquation.Kernel.hubPost_up
#print axioms MasterEquation.Kernel.hubPost_down
#print axioms MasterEquation.Kernel.size_drift_integral
#print axioms MasterEquation.Kernel.own_value_gap_drift

-- Proposition 3 (one-spoke marginal) and its Gaussian case (half-normal mixture)
#print axioms MasterEquation.SpokeMarginal.atom_exact
#print axioms MasterEquation.SpokeMarginal.spokeLead_eq_spokePost_empty
#print axioms MasterEquation.SpokeMarginal.measurable_spokeLead
#print axioms MasterEquation.SpokeMarginal.spoke_marginal_mixture
#print axioms MasterEquation.SpokeMarginal.atom_mass
#print axioms MasterEquation.SpokeMarginal.atom_eq_direction_mixture
#print axioms MasterEquation.SpokeMarginal.Ici_add_Iic_of_no_atom
#print axioms MasterEquation.SpokeMarginal.atom_half_of_common_law
#print axioms MasterEquation.SpokeMarginal.half_of_symmetric
#print axioms MasterEquation.SpokeMarginal.closed_halves_of_symmetric
#print axioms MasterEquation.SpokeMarginal.atom_half_of_symmetric
#print axioms MasterEquation.SpokeMarginal.gaussian_atom
#print axioms MasterEquation.SpokeMarginal.gaussian_spoke_atom
#print axioms MasterEquation.SpokeMarginal.leftover_scale_symmetric

-- The half-normal mean of the Gaussian case
#print axioms MasterEquation.GaussianMoment.integral_Ioi_mul_exp_neg_mul_sq
#print axioms MasterEquation.GaussianMoment.integral_Ioi_gaussianReal
#print axioms MasterEquation.GaussianMoment.two_mul_oneSided_eq
#print axioms MasterEquation.GaussianMoment.conditional_mean_eq
