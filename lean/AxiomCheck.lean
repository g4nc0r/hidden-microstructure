import MasterEquation

-- Theorem 1 (Master Equation jump), §4.1 / Appendix A
#print axioms MasterEquation.lnew_isGreatest
#print axioms MasterEquation.dust_nonneg
#print axioms MasterEquation.dustX_eq_zero_iff
#print axioms MasterEquation.dustY_eq_zero_iff
#print axioms MasterEquation.dust_mul_eq_zero
#print axioms MasterEquation.dust_both_zero_iff
#print axioms MasterEquation.exactly_one_dust_zero
#print axioms MasterEquation.slack_leftover_of_token0_binds
#print axioms MasterEquation.dust_add_eq_abs_sub
#print axioms MasterEquation.lp_below_range
#print axioms MasterEquation.lp_above_range
#print axioms MasterEquation.lnew_gs_corner

-- Theorem 2 (multi-pool mass conservation), §5.2 / Appendix C
#print axioms MasterEquation.Rebalance.mass_conservation
#print axioms MasterEquation.Rebalance.value_conservation
#print axioms MasterEquation.impacts_add_ledger_change_eq_zero
#print axioms MasterEquation.mixed_sign_of_sum_zero

-- Proposition 1 (Connector Rule), §5.1 / Appendix B
#print axioms MasterEquation.token1_binds_iff
#print axioms MasterEquation.token0_leaks
#print axioms MasterEquation.exit_above_leaks_token1
#print axioms MasterEquation.exit_below_leaks_token0
#print axioms MasterEquation.signedDustT0_pos_of_token1_leaks
#print axioms MasterEquation.signedDustT0_neg_of_token0_leaks
#print axioms MasterEquation.signedDustT1_eq_neg
#print axioms MasterEquation.concordance_nonneg
#print axioms MasterEquation.concordance_nonpos_of_neg

-- Hub-spoke kernel, Appendix D
#print axioms MasterEquation.HubSpoke.hat_diff
#print axioms MasterEquation.HubSpoke.dust_of_symmetric_requirements
#print axioms MasterEquation.HubSpoke.kernel_eq_master_jump
#print axioms MasterEquation.HubSpoke.spoke_binds_iff
#print axioms MasterEquation.HubSpoke.leftover_magnitude
#print axioms MasterEquation.HubSpoke.post_mul_eq_zero
#print axioms MasterEquation.HubSpoke.coupled_step_lipschitz
#print axioms MasterEquation.HubSpoke.coupled_step_reset
#print axioms MasterEquation.HubSpoke.lyap_post
#print axioms MasterEquation.HubSpoke.foster_drift_pointwise
#print axioms MasterEquation.HubSpoke.foster_drift_integral

-- Proposition 3 and Corollary 1, §6 / Appendix D
#print axioms MasterEquation.SpokeMarginal.spokeLimit_eq_spokePost_typical_state
#print axioms MasterEquation.SpokeMarginal.spoke_marginal_mixture
#print axioms MasterEquation.SpokeMarginal.atom_mass
#print axioms MasterEquation.SpokeMarginal.binding_prob_of_symmetric
#print axioms MasterEquation.SpokeMarginal.gaussian_binding_prob
#print axioms MasterEquation.SpokeMarginal.gaussian_spoke_atom

-- Doeblin minorisation and the (A4) route (candidate result, see README)
#print axioms MasterEquation.Doeblin.integral_sub_le_of_atom
#print axioms MasterEquation.Doeblin.abs_integral_sub_le_of_atom
#print axioms MasterEquation.HubSpoke.resetConst_le_hubLaw_atom
#print axioms MasterEquation.HubSpoke.hub_dobrushin_step
#print axioms MasterEquation.HubSpoke.resetConst_pos
#print axioms MasterEquation.HubSpoke.resetConst_le_one
#print axioms MasterEquation.HubSpoke.resetConst_le_spokeLaw_atom
#print axioms MasterEquation.HubSpoke.spoke_dobrushin_step
#print axioms MasterEquation.HubSpoke.spread_iterate

-- Corollary 1's remaining moment identity
#print axioms MasterEquation.GaussianMoment.integral_Ioi_mul_exp_neg_mul_sq
#print axioms MasterEquation.GaussianMoment.integral_Ioi_gaussianReal
#print axioms MasterEquation.GaussianMoment.two_mul_oneSided_eq
#print axioms MasterEquation.GaussianMoment.conditional_mean_eq
