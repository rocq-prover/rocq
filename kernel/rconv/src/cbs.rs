//! OCaml functions called from Rust, registered by [Rconv] and [Conversion].

use crate::cb;

cb!(ANOMALY, "rconv_anomaly");
cb!(CHECK_FOR_INTERRUPT, "rconv_check_for_interrupt");
cb!(EQ, "rconv_eq");
cb!(QEQ, "rconv_qeq");
cb!(CONSTANT_HASH, "rconv_constant_hash");
cb!(INSTANCE_EQUAL, "rconv_instance_equal");
cb!(SUBST_INSTANCE_INSTANCE, "rconv_subst_instance_instance");
cb!(SUBST_RELEVANCE, "rconv_subst_relevance");
cb!(USUBST_BINDER, "rconv_usubst_binder");
cb!(MK_SORT_SUBST, "rconv_mk_sort_subst");
cb!(SORT_EQ_UNDER, "rconv_sort_eq_under");
cb!(QVAR_IRRELEVANT, "rconv_qvar_irrelevant");
cb!(IND_RELEVANCE, "rconv_ind_relevance");
cb!(VALUE_OF, "rconv_value_of");
cb!(EVAR_EXPAND, "rconv_evar_expand");
cb!(EVAR_IRRELEVANT, "rconv_evar_irrelevant");
cb!(PROJ_MAKE, "rconv_proj_make");
cb!(UNFOLD_PROJECTION, "rconv_unfold_projection");
cb!(PRIM_KIND, "rconv_prim_kind");
cb!(PRIM_ARITY, "rconv_prim_arity");
cb!(RED_PRIM, "rconv_red_prim");
cb!(PARRAY_TO_ARRAY, "rconv_parray_to_array");
cb!(PARRAY_OF_ARRAY, "rconv_parray_of_array");
cb!(PARRAY_LENGTH, "rconv_parray_length");
cb!(MIND_PARAMS, "rconv_mind_params");
cb!(CTOR_CTX, "rconv_ctor_ctx");
cb!(CTOR_LETCTX, "rconv_ctor_letctx");
cb!(ARITY_LETCTX, "rconv_arity_letctx");
cb!(IND_NCONSTRUCTORS, "rconv_ind_nconstructors");
cb!(INVERSION_INDICES, "rconv_inversion_indices");
cb!(ETA_RECORD, "rconv_eta_record");
cb!(ETA_EXPAND_IND, "rconv_eta_expand_ind");
cb!(ETA_EXPAND_CONSTRUCTOR, "rconv_eta_expand_constructor");
cb!(IND_CUMUL_INFO, "rconv_ind_cumul_info");
cb!(CTOR_CUMUL_INFO, "rconv_ctor_cumul_info");
cb!(IRRELEVANT_VARIANCE, "rconv_irrelevant_variance");
cb!(ARRAY_VARIANCE, "rconv_array_variance");
cb!(ALL_TRANSPARENT, "rconv_all_transparent");
cb!(STD_FLAGS, "rconv_std_flags");
cb!(SHARE, "rconv_share");
cb!(CONV_FLEX, "rconv_conv_flex");
cb!(IS_ARRAY_TYPE, "rconv_is_array_type");
cb!(IRR_FLEX, "rconv_irr_flex");
cb!(UNFOLD_LEFT, "rconv_unfold_left");
cb!(MK_LAMBDA, "rconv_mk_lambda");
cb!(INSTANCE_OF_ARRAY, "rconv_instance_of_array");
cb!(PS_MAKE, "rconv_ps_make");
cb!(PS_ADD_TERM, "rconv_ps_add_term");
cb!(PS_FINALIZE, "rconv_ps_finalize");
cb!(INSTANCE_PATTERN_MATCH, "rconv_instance_pattern_match");
cb!(SORT_PATTERN_MATCH, "rconv_sort_pattern_match");
cb!(CHECKED_UNIVERSES, "rconv_checked_universes");
cb!(COMPARE_SORTS, "rconv_compare_sorts");
cb!(COMPARE_INSTANCES, "rconv_compare_instances");
cb!(COMPARE_CUMUL_INSTANCES, "rconv_compare_cumul_instances");
cb!(RESULT_OK, "rconv_result_ok");
cb!(RESULT_ERROR, "rconv_result_error");

/* Kinds for [rconv_eq] */
pub const EQ_CONSTANT_CAN: isize = 0;
pub const EQ_IND_CAN: isize = 1;
pub const EQ_PROJ_REPR_CAN: isize = 2;
pub const EQ_EVAR: isize = 3;
pub const EQ_PRIM: isize = 4;
pub const EQ_CONSTANT_USER: isize = 5;
pub const EQ_IND_USER: isize = 6;
pub const EQ_CONSTRUCT_USER: isize = 7;
pub const EQ_PROJ_USER: isize = 8;
pub const EQ_ID: isize = 9;
pub const EQ_UINT63: isize = 10;
pub const EQ_FLOAT64: isize = 11;
pub const EQ_PSTRING: isize = 12;
pub const EQ_SORT: isize = 13;

/* Kinds for [rconv_qeq] */
pub const QEQ_IND: isize = 0;
pub const QEQ_CONSTRUCT: isize = 1;
pub const QEQ_CONSTANT: isize = 2;
pub const QEQ_PROJ_REPR: isize = 3;

/* Anomalies */
pub const AN_PATTERN_VAR: isize = 0;
pub const AN_PARTIAL_CTOR: isize = 1;
pub const AN_LAMBDA_ILLTYPED: isize = 2;
pub const AN_LAMBDA_UNREDUCED: isize = 3;
pub const AN_CTOR_UNREDUCED: isize = 4;
