# Ownership of the EG sessions

Each session owns one file and proves its STUB lemmas, and the stub constants where the row names
them. Every session proves against frozen statements only, so all of them can run at once. The
hours are estimates, and every card is at most ~6 hours.

| Card | File | STUB lemmas and constants | Hours |
| --- | --- | --- | --- |
| LW-Q | `theories/Front/LowerQueries.v` | `query_pats_fresh`, `query_pats_complete`, `query_pats_sound` | ~3 |
| LW-BU | `theories/Front/LowerBuilds.v` | `build_pats_fresh`, `build_pats_present_sound`, `build_pats_derivation`, `build_pats_derivation_sound` | ~4 |
| LW-M | `theories/Front/LowerModels.v` | `query_pats_meaning`, `build_pats_model`, `build_pats_represents` | ~4 |
| LW-BD | `theories/Front/LowerBodies.v` | `query_body_matches`, `query_body_lets`, `checks_last_matches` | ~5 |
| LW-K | `theories/Front/LowerKinds.v` | `relational_kinds_ok`, `head_vars_bound` | ~4 |
| LW-S | `theories/Front/LowerScopes.v` | `clause_rule_scoped` | ~4 |
| LW-C | `theories/Front/LowerComplete.v` | `lower_complete`, `lower_closed` | ~4 |
| LW-SD | `theories/Front/LowerSound.v` | `lower_sound` | ~5 |
| LW-V | `theories/Front/LowerValid.v` | `lower_valid` | ~5 |
| R-1 | `theories/Front/RunnerFacts.v` | `plan_ok`, `seed_rows`, `seed_ready`, `holds_spec`, `seed_sat`, `solve_keeps`, `saturate_keeps` | ~5.5 |
| RT-1 | `theories/Front/RunnerSeedTime.v` | constant `c_runner`, `T_seed_amort`, `T_seed_le`, `seed_complexity`, `T_solve_split`, `T_holds_le`, `holds_complexity`, `T_same_cell_le`, `same_cell_complexity` | ~6 |
| RT-2 | `theories/Front/RunnerTermsTime.v` | constant `c_terms`, `add_terms_unit`, `T_add_term_amort`, `T_add_terms_amort`, `add_term_complexity`, `add_terms_complexity` | ~5.5 |
| RT-3 | `theories/Front/RunnerTime.v` | constant `c_saturate`, `solve_complexity`, `T_saturate_split`, `saturate_complexity`, `T_equal_split`, `equal_complexity` | ~5.5 |
| R-2 | `theories/Front/Relational.v` | `solve_sound`, `solve_complete`, `solve_saturates` | ~4 |
| CC-F | `theories/Front/ClosureFixpoint.v` | `classes_closed` | ~3 |
| CC-A | `theories/Front/ClosureClasses.v` | `universe_eqs`, `universe_args`, `rep_of_universe`, `rep_of_sound`, `rep_of_eqs`, `rep_of_cong` | ~4.5 |
| CC-B | `theories/Front/ClosureForms.v` | `nf_universe`, `nf_app`, `nf_lit`, `nf_sound` | ~6 |
| CC-C | `theories/Front/CongruenceClosure.v` | `closure_model` | ~4 |
| REF-1 | `theories/Front/CongruenceInstances.v` | `instances_listed`, `instances_apps` | ~5 |
| REF-2 | `theories/Front/CongruenceRef.v` | `congruent_closure`, `exact_model` | ~4 |
| G-1 | `theories/Front/GroundSound.v` | `congruent_denote`, `solve_sound` | ~5 |
| G-2a | `theories/Front/GroundClasses.v` | `outcome_rows`, `class_sat`, `class_nu_same` | ~6 |
| G-2b | `theories/Front/GroundSatisfies.v` | `class_satisfies` | ~3.5 |
| G-3a | `theories/Front/GroundBuild.v` | `instance_built` | ~4 |
| G-3b | `theories/Front/GroundComplete.v` | `solve_complete`, `solve_builds` | ~3 |
| RW-1 | `theories/Front/RewriteTerms.v` | `add_terms_sat`, `add_terms_ready` | ~6 |
| RW-2 | `theories/Front/RewriteSound.v` | `saturate_sound`, `saturate_represents`, `equal_sound` | ~5 |
| RW-3 | `theories/Front/RewriteMatch.v` | `query_pat_complete` | ~4 |
| RW-4 | `theories/Front/RewriteClosed.v` | `saturate_closed` | ~5 |
| LT-1 | `theories/Front/LatticeSound.v` | `lattice_model`, `solve_sound` | ~5 |
| LT-2 | `theories/Front/LatticeComplete.v` | `lower_assigned`, `solve_complete` | ~4.5 |
| EX | `theories/Front/Extraction.v` | `fits_inventory`, `decode_agrees_unfold`, `cheapest_represents`, `cheapest_optimal` | ~4 |
| EX-T | `theories/Front/ExtractionTime.v` | constant `c_extraction`, `T_decode_le`, `decode_complexity`, `T_cheapest_split`, `cheapest_complexity` | ~6 |
| AN-1 | `theories/Clients/Andersen.v` | `facts_rows_ok`, `seed_rows`, `seed_loaded`, `seed_wf`, `points_spec`, `solve_exact` | ~4 |
| AN-2 | `theories/Clients/AndersenTime.v` | constants `k_rules`, `k_seed`, `k_wrap`, `c_andersen`, `T_seed_le`, `T_compile_le`, `T_points_le`, `T_solve_le`, `T_solve_split`, and the four `*_complexity` fields | ~6 |
| ST-1 | `theories/Clients/Steensgaard.v` | `facts_rows_ok`, `seed_rows`, `seed_loaded`, `seed_wf`, `solve_covers` | ~6 |
| ST-2 | `theories/Clients/SteensgaardExact.v` | `pointer_congruence_back`, `solve_exact` | ~5 |
| ST-3 | `theories/Clients/SteensgaardTime.v` | `T_seed_le`, `T_solve_le`, `saturated_equations`, `T_solve_split` | ~4 |
