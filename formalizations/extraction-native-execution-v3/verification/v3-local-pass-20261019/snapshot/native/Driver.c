// Lean compiler output
// Module: Driver
// Imports: public import Init public meta import Init public import Lean.Replay public import Lean.Util.Path
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isAxiom(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_List_zipIdxTR___redArg(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_get_stdout();
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* l_Lean_Kernel_Environment_replay(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_List_repr___at___00Lean_Environment_dbgFormatAsyncState_spec__2___redArg(lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instReprExpr_repr(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isTheorem(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_internal_set_max_memory(size_t);
LEAN_EXPORT lean_object* l_NativeExecutionV3_setMaximumMemory___boxed(lean_object*, lean_object*);
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "EffectiveEncoding"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__0 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "fullyAssembledInputRun_erase"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__1 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__1_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__2_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__1_value),LEAN_SCALAR_PTR_LITERAL(140, 117, 67, 30, 216, 246, 43, 35)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__2 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__2_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "fullyAssembledInputRun_accountedPrimitiveActions"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__3 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__3_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__4_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 169, 108, 3, 30, 72, 203, 64)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__4 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__4_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "fullyAssembledInputRun_fidelity"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__5 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__5_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__6_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__5_value),LEAN_SCALAR_PTR_LITERAL(102, 70, 25, 36, 163, 175, 232, 24)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__6 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__6_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "retainedInputTargetRun_cached"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__7 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__7_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__8_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__7_value),LEAN_SCALAR_PTR_LITERAL(190, 217, 232, 128, 83, 122, 190, 84)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__8 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__8_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "retainedInputTargetRun_cache"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__9 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__9_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__10_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__9_value),LEAN_SCALAR_PTR_LITERAL(123, 19, 69, 92, 213, 156, 179, 9)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__10 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__10_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__11 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__11_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__8_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__11_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__12 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__12_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__6_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__12_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__13 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__13_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__4_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__13_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__14 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__14_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__2_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__14_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__15 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__15_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "scannedNativeDescriptorRun_result"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__16 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__16_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__17_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__16_value),LEAN_SCALAR_PTR_LITERAL(167, 74, 173, 204, 5, 200, 99, 183)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__17 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__17_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "scannedNativeDescriptorRun_scanActions"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__18 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__18_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__19_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__18_value),LEAN_SCALAR_PTR_LITERAL(30, 80, 48, 135, 238, 73, 210, 34)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__19 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__19_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "retainedAssembledTargetRun_erase"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__20 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__20_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__21_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__20_value),LEAN_SCALAR_PTR_LITERAL(95, 232, 6, 7, 19, 123, 126, 6)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__21 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__21_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "retainedAssembledTargetRun_cached"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__22 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__22_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__23_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__22_value),LEAN_SCALAR_PTR_LITERAL(173, 171, 184, 91, 140, 49, 78, 41)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__23 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__23_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__23_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__15_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__24 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__24_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__21_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__24_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__25 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__25_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__19_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__25_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__26 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__26_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__17_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__26_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__27 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__27_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CircuitRecursion"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__28 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "assembledInputCachedRun_actions_degree13"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__29 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__29_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__30_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__29_value),LEAN_SCALAR_PTR_LITERAL(102, 251, 92, 115, 196, 111, 126, 159)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__30 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__30_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "assembledInputPairWord_program"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__31 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__31_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__32_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__31_value),LEAN_SCALAR_PTR_LITERAL(108, 41, 97, 96, 33, 191, 39, 247)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__32 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__32_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "nativeBooleanRankProgram_ranked"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__33 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__33_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__34_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__33_value),LEAN_SCALAR_PTR_LITERAL(99, 174, 39, 7, 140, 126, 9, 139)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__34 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__34_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "nativeBooleanRankProgram_booleanActions_polynomial"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__35 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__35_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__36_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__35_value),LEAN_SCALAR_PTR_LITERAL(249, 179, 200, 149, 211, 53, 153, 252)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__36 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__36_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__36_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__27_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__37 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__37_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__34_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__37_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__38 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__38_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__32_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__38_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__39 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__39_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__30_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__39_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__40 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__40_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "inputCachedRun_onlineActions_degree338"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__41 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__41_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__42_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__41_value),LEAN_SCALAR_PTR_LITERAL(229, 142, 243, 36, 3, 72, 212, 88)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__42 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__42_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "inputCachedRun_readActions_degree73"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__43 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__43_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__44_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__43_value),LEAN_SCALAR_PTR_LITERAL(206, 184, 139, 165, 122, 159, 22, 241)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__44 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__44_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "assembledInputCachedRun_erase"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__45 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__45_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__46_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__45_value),LEAN_SCALAR_PTR_LITERAL(239, 0, 83, 130, 108, 127, 227, 144)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__46 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__46_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "assembledInputCachedRun_onlineActions_degree338"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__47 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__47_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__48_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__47_value),LEAN_SCALAR_PTR_LITERAL(12, 172, 218, 59, 71, 104, 192, 140)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__48 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__48_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__48_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__40_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__49 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__49_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__46_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__49_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__50 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__50_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__44_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__50_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__51 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__51_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__42_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__51_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__52 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__52_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "RationalGateBinary"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__53 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__53_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "nativeEntry_correct"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__54 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__54_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__53_value),LEAN_SCALAR_PTR_LITERAL(174, 80, 150, 245, 249, 67, 252, 100)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__55_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__54_value),LEAN_SCALAR_PTR_LITERAL(189, 72, 113, 232, 63, 103, 182, 54)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__55 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__55_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "nativeEntryProgram_normalization_actions"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__56 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__56_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__53_value),LEAN_SCALAR_PTR_LITERAL(174, 80, 150, 245, 249, 67, 252, 100)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__57_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__56_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 124, 118, 173, 4, 149, 157)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__57 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__57_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "RationalGateInterface"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__58 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__58_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "rationalGate_inverse"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__59 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__59_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__58_value),LEAN_SCALAR_PTR_LITERAL(160, 46, 47, 197, 66, 4, 226, 11)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__60_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__59_value),LEAN_SCALAR_PTR_LITERAL(101, 115, 73, 14, 128, 235, 240, 117)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__60 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__60_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "RationalGateUniversality"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__61 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__61_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "rationalGate_dense"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__62 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__62_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__61_value),LEAN_SCALAR_PTR_LITERAL(21, 67, 73, 226, 127, 94, 60, 140)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__63_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__62_value),LEAN_SCALAR_PTR_LITERAL(253, 97, 225, 184, 134, 177, 187, 198)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__63 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__63_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__63_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__52_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__64 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__64_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__60_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__64_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__65 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__65_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__57_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__65_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__66 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__66_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__55_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__66_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__67 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__67_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ConcreteNativeExtraction"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__68 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "concrete_assembled_compiler_exists"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__69 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__69_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__70_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__69_value),LEAN_SCALAR_PTR_LITERAL(245, 195, 91, 172, 81, 196, 241, 124)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__70 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__70_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "offlineNet_exists"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__71 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__71_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__72_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__71_value),LEAN_SCALAR_PTR_LITERAL(141, 238, 0, 89, 222, 231, 197, 121)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__72 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__72_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "queried_gate_height"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__73 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__73_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__74_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__73_value),LEAN_SCALAR_PTR_LITERAL(21, 69, 162, 16, 201, 180, 206, 61)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__74 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__74_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "nativeEntry_decode"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__75 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__75_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__53_value),LEAN_SCALAR_PTR_LITERAL(174, 80, 150, 245, 249, 67, 252, 100)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__76_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__75_value),LEAN_SCALAR_PTR_LITERAL(108, 100, 23, 75, 240, 200, 55, 143)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__76 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__76_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__76_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__67_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__77 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__77_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__74_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__77_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__78 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__78_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__72_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__78_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__79 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__79_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__70_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__79_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__80 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__80_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "assembledRun_length"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__81 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__81_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__82_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__81_value),LEAN_SCALAR_PTR_LITERAL(144, 253, 7, 146, 142, 0, 159, 17)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__82 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__82_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "assembledRun_fidelity"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__83 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__83_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__84_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__83_value),LEAN_SCALAR_PTR_LITERAL(66, 82, 165, 225, 248, 17, 245, 139)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__84 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__84_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "assembledRun_accounted_actions"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__85 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__85_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__86_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__85_value),LEAN_SCALAR_PTR_LITERAL(186, 15, 253, 119, 231, 197, 3, 90)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__86 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__86_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "assembledRun_inverse_calls"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__87 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__87_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__88_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__87_value),LEAN_SCALAR_PTR_LITERAL(60, 184, 165, 15, 151, 209, 9, 67)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__88 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__88_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__88_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__80_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__89 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__89_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__86_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__89_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__90 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__90_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__84_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__90_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__91 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__91_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__82_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__91_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__92 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__92_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "assembledRun_word"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__93 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__93_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__94_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__93_value),LEAN_SCALAR_PTR_LITERAL(113, 17, 153, 80, 105, 1, 191, 44)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__94 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__94_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "assembledRun_erase"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__95 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__95_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__96_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__95_value),LEAN_SCALAR_PTR_LITERAL(183, 206, 153, 34, 247, 38, 250, 159)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__96 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__96_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "assembledRun_word_eq_inputRun"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__97 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__97_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__98_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__97_value),LEAN_SCALAR_PTR_LITERAL(179, 69, 112, 238, 22, 38, 252, 10)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__98 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__98_value;
static const lean_string_object l_NativeExecutionV3_theoremNames___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "assembledRun_uses_finite_library"};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__99 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__99_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__100_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__100_value_aux_0),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__99_value),LEAN_SCALAR_PTR_LITERAL(6, 120, 186, 132, 20, 69, 156, 174)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__100 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__100_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__100_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__92_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__101 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__101_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__98_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__101_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__102 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__102_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__96_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__102_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__103 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__103_value;
static const lean_ctor_object l_NativeExecutionV3_theoremNames___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_theoremNames___closed__94_value),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__103_value)}};
static const lean_object* l_NativeExecutionV3_theoremNames___closed__104 = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__104_value;
LEAN_EXPORT const lean_object* l_NativeExecutionV3_theoremNames = (const lean_object*)&l_NativeExecutionV3_theoremNames___closed__104_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "FullyAssembledInputResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__0 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__0_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "erase"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__1 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__1_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__2_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 233, 101, 148, 38, 47, 72, 42)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__2_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__1_value),LEAN_SCALAR_PTR_LITERAL(95, 131, 238, 205, 227, 102, 168, 157)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__2 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__2_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "accountedPrimitiveActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__3 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__3_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__4_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 233, 101, 148, 38, 47, 72, 42)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__4_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__3_value),LEAN_SCALAR_PTR_LITERAL(248, 122, 32, 122, 196, 86, 193, 212)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__4 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__4_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fullyAssembledInputRun"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__5 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__5_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__6_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__5_value),LEAN_SCALAR_PTR_LITERAL(62, 159, 185, 221, 206, 84, 246, 227)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__6 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__6_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "RetainedInputTargetResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__7 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__7_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "accountedActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__8 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__8_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__9_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__7_value),LEAN_SCALAR_PTR_LITERAL(25, 53, 200, 88, 242, 242, 161, 241)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__9_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 103, 113, 10, 164, 254, 21, 134)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__9 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__9_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "providerActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__10 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__10_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__11_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__7_value),LEAN_SCALAR_PTR_LITERAL(25, 53, 200, 88, 242, 242, 161, 241)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__11_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__10_value),LEAN_SCALAR_PTR_LITERAL(203, 93, 75, 119, 172, 52, 161, 170)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__11 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__11_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "RetainedNativeTargetResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__12 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__12_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__13_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__12_value),LEAN_SCALAR_PTR_LITERAL(213, 198, 204, 195, 180, 195, 96, 93)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__13_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__10_value),LEAN_SCALAR_PTR_LITERAL(15, 224, 99, 110, 245, 234, 187, 111)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__13 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__13_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "buildNativeTargetPrograms"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__14 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__14_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__15_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__14_value),LEAN_SCALAR_PTR_LITERAL(131, 202, 117, 178, 131, 70, 191, 163)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__15 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__15_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__16 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__16_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__13_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__16_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__17 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__17_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__11_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__17_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__18 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__18_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__9_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__18_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__19 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__19_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__6_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__19_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__20 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__20_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__4_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__20_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__21 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__21_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__2_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__21_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__22 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__22_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "ScannedGeneratedRun"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__23 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__23_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "scanActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__24 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__24_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__25_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__23_value),LEAN_SCALAR_PTR_LITERAL(5, 187, 188, 20, 141, 154, 244, 253)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__25_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__24_value),LEAN_SCALAR_PTR_LITERAL(200, 195, 251, 104, 124, 79, 84, 86)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__25 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__25_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NativeBinaryRankResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__26 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__26_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "encodingActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__27 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__27_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__28_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__26_value),LEAN_SCALAR_PTR_LITERAL(120, 9, 112, 200, 121, 19, 206, 164)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__28_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__27_value),LEAN_SCALAR_PTR_LITERAL(45, 111, 107, 39, 131, 75, 65, 10)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__28 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__28_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "BinaryGeneratedRun"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__29 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__29_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__30_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__29_value),LEAN_SCALAR_PTR_LITERAL(163, 73, 212, 151, 56, 223, 68, 6)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__30_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__27_value),LEAN_SCALAR_PTR_LITERAL(138, 98, 205, 89, 236, 32, 25, 42)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__30 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__30_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "retainedAssembledTargetRun"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__31 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__31_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__32_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__31_value),LEAN_SCALAR_PTR_LITERAL(209, 71, 54, 89, 232, 112, 184, 6)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__32 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__32_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "RetainedAssembledTargetResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__33 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__33_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__34_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__33_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 212, 33, 38, 16, 94, 43)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__34_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 137, 170, 49, 250, 148, 193, 30)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__34 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__34_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "assemblyActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__35 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__35_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__36_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__33_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 212, 33, 38, 16, 94, 43)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__36_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__35_value),LEAN_SCALAR_PTR_LITERAL(127, 241, 182, 5, 3, 105, 150, 148)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__36 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__36_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "compileAssembledWord"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__37 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__37_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__38_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__37_value),LEAN_SCALAR_PTR_LITERAL(120, 193, 191, 54, 47, 27, 36, 69)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__38 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__38_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__38_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__22_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__39 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__39_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__36_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__39_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__40 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__40_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__34_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__40_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__41 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__41_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__32_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__41_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__42 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__42_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__30_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__42_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__43 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__43_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__28_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__43_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__44 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__44_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__25_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__44_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__45 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__45_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "nativeBooleanRankProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__46 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__46_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__47_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__46_value),LEAN_SCALAR_PTR_LITERAL(135, 210, 151, 75, 82, 219, 201, 255)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__47 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__47_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "NativeBooleanRankResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__48 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__48_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "booleanActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__49 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__49_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__50_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__48_value),LEAN_SCALAR_PTR_LITERAL(235, 28, 27, 232, 219, 59, 247, 144)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__50_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__49_value),LEAN_SCALAR_PTR_LITERAL(105, 38, 134, 182, 61, 211, 131, 44)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__50 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__50_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "nativeTripleScanProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__51 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__51_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__52_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__51_value),LEAN_SCALAR_PTR_LITERAL(13, 91, 228, 66, 84, 88, 7, 185)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__52 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__52_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NativeTripleComparison"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__53 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__53_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "actions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__54 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__54_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__55_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__53_value),LEAN_SCALAR_PTR_LITERAL(50, 2, 163, 147, 41, 213, 88, 63)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__55_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__54_value),LEAN_SCALAR_PTR_LITERAL(120, 243, 46, 39, 145, 133, 219, 249)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__55 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__55_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "NativeTripleScanResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__56 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__56_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "comparisonActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__57 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__57_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__58_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__56_value),LEAN_SCALAR_PTR_LITERAL(75, 31, 175, 16, 152, 62, 136, 230)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__58_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__57_value),LEAN_SCALAR_PTR_LITERAL(15, 97, 159, 117, 47, 150, 125, 242)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__58 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__58_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "scannedRankWordProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__59 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__59_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__60_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__59_value),LEAN_SCALAR_PTR_LITERAL(103, 215, 28, 183, 114, 95, 246, 108)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__60 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__60_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "scannedNativeDescriptorRun"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__61 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__61_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 106, 89, 70, 113, 44, 134, 199)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__62_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__61_value),LEAN_SCALAR_PTR_LITERAL(5, 74, 10, 102, 95, 160, 38, 98)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__62 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__62_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__62_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__45_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__63 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__63_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__60_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__63_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__64 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__64_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__58_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__64_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__65 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__65_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__55_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__65_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__66 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__66_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__52_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__66_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__67 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__67_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__50_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__67_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__68 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__68_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__47_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__68_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__69 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__69_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "InputArithmeticWordResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__70 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__70_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "numericalActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__71 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__71_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__72_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__70_value),LEAN_SCALAR_PTR_LITERAL(94, 3, 40, 66, 245, 176, 88, 214)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__72_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__71_value),LEAN_SCALAR_PTR_LITERAL(225, 12, 158, 127, 82, 61, 161, 154)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__72 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__72_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "readActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__73 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__73_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__74_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__70_value),LEAN_SCALAR_PTR_LITERAL(94, 3, 40, 66, 245, 176, 88, 214)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__74_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__73_value),LEAN_SCALAR_PTR_LITERAL(180, 179, 91, 38, 161, 214, 243, 188)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__74 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__74_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "onlineActions"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__75 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__75_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__76_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__70_value),LEAN_SCALAR_PTR_LITERAL(94, 3, 40, 66, 245, 176, 88, 214)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__76_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__75_value),LEAN_SCALAR_PTR_LITERAL(230, 60, 244, 28, 131, 15, 171, 240)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__76 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__76_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "nativeCacheInputRead"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__77 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__77_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__78_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__77_value),LEAN_SCALAR_PTR_LITERAL(37, 253, 3, 49, 249, 151, 86, 246)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__78 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__78_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "nativeListLookup"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__79 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__79_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__80_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__79_value),LEAN_SCALAR_PTR_LITERAL(228, 105, 81, 255, 84, 43, 22, 186)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__80 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__80_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "NativeListLookupTrace"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__81 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__81_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__82_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__81_value),LEAN_SCALAR_PTR_LITERAL(182, 234, 107, 6, 241, 54, 49, 91)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__82_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__54_value),LEAN_SCALAR_PTR_LITERAL(76, 23, 25, 68, 133, 13, 197, 119)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__82 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__82_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__82_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__69_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__83 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__83_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__80_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__83_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__84 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__84_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__78_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__84_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__85 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__85_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__76_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__85_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__86 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__86_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__74_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__86_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__87 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__87_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__72_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__87_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__88 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__88_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "InputListAssemblyTrace"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__89 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__89_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inverseCalls"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__90 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__90_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__91_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__91_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__91_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__89_value),LEAN_SCALAR_PTR_LITERAL(233, 96, 109, 41, 20, 68, 228, 162)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__91_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__90_value),LEAN_SCALAR_PTR_LITERAL(234, 193, 154, 23, 182, 221, 200, 30)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__91 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__91_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "assembleCorrectedInput"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__92 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__92_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__93_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__92_value),LEAN_SCALAR_PTR_LITERAL(188, 245, 76, 220, 34, 182, 249, 8)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__93 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__93_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "assembledInputCorrection"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__94 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__94_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__95_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__94_value),LEAN_SCALAR_PTR_LITERAL(80, 90, 207, 172, 125, 11, 172, 74)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__95 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__95_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "assembledInputPairWord"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__96 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__96_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__97_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__97_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__96_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 125, 16, 0, 142, 99, 249)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__97 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__97_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "AssembledInputWordResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__98 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__98_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__99_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__99_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__99_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__98_value),LEAN_SCALAR_PTR_LITERAL(114, 33, 126, 77, 21, 101, 72, 217)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__99_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__75_value),LEAN_SCALAR_PTR_LITERAL(138, 178, 186, 40, 19, 28, 118, 231)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__99 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__99_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "assembledInputCachedRun"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__100 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__100_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__101_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__100_value),LEAN_SCALAR_PTR_LITERAL(196, 194, 201, 248, 205, 165, 50, 44)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__101 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__101_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "inputCachedRun"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__102 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__102_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__103_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__103_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__102_value),LEAN_SCALAR_PTR_LITERAL(121, 9, 0, 239, 179, 70, 89, 201)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__103 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__103_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__103_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__88_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__104 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__104_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__101_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__104_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__105 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__105_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__99_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__105_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__106 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__106_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__97_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__106_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__107 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__107_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__95_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__107_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__108 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__108_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__93_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__108_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__109 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__109_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__91_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__109_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__110 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__110_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ListAssemblyTrace"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__111 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__111_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "copies"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__112 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__112_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__113_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__113_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__111_value),LEAN_SCALAR_PTR_LITERAL(155, 41, 155, 112, 84, 69, 7, 179)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__113_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__112_value),LEAN_SCALAR_PTR_LITERAL(214, 237, 251, 139, 70, 180, 50, 171)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__113 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__113_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "listAppendProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__114 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__114_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__115_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__114_value),LEAN_SCALAR_PTR_LITERAL(16, 248, 64, 196, 133, 234, 0, 240)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__115 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__115_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "listReverseMapIntoProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__116 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__116_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__117_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__117_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__116_value),LEAN_SCALAR_PTR_LITERAL(12, 193, 109, 27, 169, 30, 221, 196)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__117 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__117_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "instructionInverseProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__118 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__118_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__119_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__118_value),LEAN_SCALAR_PTR_LITERAL(2, 105, 238, 47, 120, 170, 240, 99)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__119 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__119_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__120_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__120_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__89_value),LEAN_SCALAR_PTR_LITERAL(233, 96, 109, 41, 20, 68, 228, 162)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__120 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__120_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__121_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__121_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__89_value),LEAN_SCALAR_PTR_LITERAL(233, 96, 109, 41, 20, 68, 228, 162)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__121_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__54_value),LEAN_SCALAR_PTR_LITERAL(255, 90, 167, 237, 125, 180, 50, 139)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__121 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__121_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__121_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__110_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__122 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__122_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__120_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__122_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__123 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__123_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__119_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__123_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__124 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__124_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__117_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__124_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__125 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__125_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__115_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__125_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__126 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__126_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__113_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__126_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__127 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__127_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rationalGate"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__128 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__128_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__129_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__58_value),LEAN_SCALAR_PTR_LITERAL(160, 46, 47, 197, 66, 4, 226, 11)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__129_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__128_value),LEAN_SCALAR_PTR_LITERAL(194, 144, 13, 26, 116, 238, 73, 54)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__129 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__129_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "binaryPacketInputProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__130 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__130_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__131_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__131_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__130_value),LEAN_SCALAR_PTR_LITERAL(176, 57, 121, 207, 28, 104, 43, 144)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__131 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__131_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "BinaryPacketInputResult"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__132 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__132_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__133_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__133_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__133_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__132_value),LEAN_SCALAR_PTR_LITERAL(106, 126, 134, 165, 216, 17, 222, 43)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__133_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__54_value),LEAN_SCALAR_PTR_LITERAL(192, 150, 249, 121, 229, 34, 124, 221)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__133 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__133_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "binaryTrimProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__134 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__134_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__135_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__135_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__134_value),LEAN_SCALAR_PTR_LITERAL(103, 114, 142, 27, 127, 5, 26, 68)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__135 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__135_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "signedBinaryNormalizeProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__136 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__136_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__137_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__137_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__136_value),LEAN_SCALAR_PTR_LITERAL(209, 110, 117, 180, 13, 17, 253, 85)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__137 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__137_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__138_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__138_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__111_value),LEAN_SCALAR_PTR_LITERAL(155, 41, 155, 112, 84, 69, 7, 179)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__138 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__138_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__139_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__28_value),LEAN_SCALAR_PTR_LITERAL(218, 44, 111, 97, 46, 28, 192, 9)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__139_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__139_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__111_value),LEAN_SCALAR_PTR_LITERAL(155, 41, 155, 112, 84, 69, 7, 179)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__139_value_aux_1),((lean_object*)&l_NativeExecutionV3_modelNames___closed__54_value),LEAN_SCALAR_PTR_LITERAL(133, 65, 191, 211, 231, 184, 205, 143)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__139 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__139_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__139_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__127_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__140 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__140_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__138_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__140_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__141 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__141_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__137_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__141_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__142 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__142_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__135_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__142_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__143 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__143_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__133_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__143_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__144 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__144_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__131_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__144_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__145 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__145_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__129_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__145_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__146 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__146_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfflineNet"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__147 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__147_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__148_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__148_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__147_value),LEAN_SCALAR_PTR_LITERAL(165, 112, 88, 10, 7, 0, 211, 87)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__148 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__148_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "assembledRun"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__149 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__149_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__150_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__150_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__149_value),LEAN_SCALAR_PTR_LITERAL(39, 155, 147, 103, 167, 87, 87, 121)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__150 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__150_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "assembledPrimitiveBound"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__151 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__151_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__152_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__152_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__151_value),LEAN_SCALAR_PTR_LITERAL(169, 22, 234, 167, 83, 25, 187, 42)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__152 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__152_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "gateHeightCoefficient"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__153 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__153_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__154_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__154_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__153_value),LEAN_SCALAR_PTR_LITERAL(236, 83, 230, 63, 3, 81, 167, 226)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__154 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__154_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "nativeEntryProgram"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__155 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__155_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__156_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__53_value),LEAN_SCALAR_PTR_LITERAL(174, 80, 150, 245, 249, 67, 252, 100)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__156_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__155_value),LEAN_SCALAR_PTR_LITERAL(237, 185, 136, 27, 136, 79, 233, 77)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__156 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__156_value;
static const lean_string_object l_NativeExecutionV3_modelNames___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "nativeEntry"};
static const lean_object* l_NativeExecutionV3_modelNames___closed__157 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__157_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__158_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__53_value),LEAN_SCALAR_PTR_LITERAL(174, 80, 150, 245, 249, 67, 252, 100)}};
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__158_value_aux_0),((lean_object*)&l_NativeExecutionV3_modelNames___closed__157_value),LEAN_SCALAR_PTR_LITERAL(217, 39, 68, 87, 46, 2, 60, 122)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__158 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__158_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__158_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__146_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__159 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__159_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__156_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__159_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__160 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__160_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__154_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__160_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__161 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__161_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__152_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__161_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__162 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__162_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__150_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__162_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__163 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__163_value;
static const lean_ctor_object l_NativeExecutionV3_modelNames___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_modelNames___closed__148_value),((lean_object*)&l_NativeExecutionV3_modelNames___closed__163_value)}};
static const lean_object* l_NativeExecutionV3_modelNames___closed__164 = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__164_value;
LEAN_EXPORT const lean_object* l_NativeExecutionV3_modelNames = (const lean_object*)&l_NativeExecutionV3_modelNames___closed__164_value;
LEAN_EXPORT lean_object* l_NativeExecutionV3_emit(lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_emit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00NativeExecutionV3_collect_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00NativeExecutionV3_collect_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_NativeExecutionV3_collect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Missing dependency "};
static const lean_object* l_NativeExecutionV3_collect___closed__0 = (const lean_object*)&l_NativeExecutionV3_collect___closed__0_value;
LEAN_EXPORT lean_object* l_NativeExecutionV3_collect(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_NativeExecutionV3_collected___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_collected___closed__0;
static lean_once_cell_t l_NativeExecutionV3_collected___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_collected___closed__1;
LEAN_EXPORT lean_object* l_NativeExecutionV3_collected(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_collected___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unexpected axiom "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "propext"};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 150, 49, 30, 125, 3, 39, 172)}};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Classical"};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 236, 220, 79, 38, 141, 161, 150)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 246, 154, 249, 193, 98, 251, 55)}};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sound"};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__8_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(255, 255, 230, 69, 40, 79, 199, 28)}};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__8_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__9_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__5_value),((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__9_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__10_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__2_value),((lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__10_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__11_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Unsafe/partial dependency "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_checkSafety(lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_checkSafety___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00NativeExecutionV3_sortedNames_spec__0(lean_object*, lean_object*);
static const lean_closure_object l_NativeExecutionV3_sortedNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decidableLT___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_NativeExecutionV3_sortedNames___closed__0 = (const lean_object*)&l_NativeExecutionV3_sortedNames___closed__0_value;
LEAN_EXPORT lean_object* l_NativeExecutionV3_sortedNames(lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_sortedNames___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00NativeExecutionV3_axiomNames_spec__0(lean_object*, lean_object*);
static const lean_array_object l_NativeExecutionV3_axiomNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_NativeExecutionV3_axiomNames___closed__0 = (const lean_object*)&l_NativeExecutionV3_axiomNames___closed__0_value;
LEAN_EXPORT lean_object* l_NativeExecutionV3_axiomNames(lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_axiomNames___boxed(lean_object*);
static const lean_string_object l_NativeExecutionV3_writeLines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_NativeExecutionV3_writeLines___closed__0 = (const lean_object*)&l_NativeExecutionV3_writeLines___closed__0_value;
LEAN_EXPORT lean_object* l_NativeExecutionV3_writeLines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_writeLines___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_jsonFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_jsonFile___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_NativeExecutionV3_info___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Missing declaration "};
static const lean_object* l_NativeExecutionV3_info___closed__0 = (const lean_object*)&l_NativeExecutionV3_info___closed__0_value;
LEAN_EXPORT lean_object* l_NativeExecutionV3_info(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_info___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_NativeExecutionV3_typeText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "name "};
static const lean_object* l_NativeExecutionV3_typeText___closed__0 = (const lean_object*)&l_NativeExecutionV3_typeText___closed__0_value;
static const lean_string_object l_NativeExecutionV3_typeText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nlevels "};
static const lean_object* l_NativeExecutionV3_typeText___closed__1 = (const lean_object*)&l_NativeExecutionV3_typeText___closed__1_value;
static const lean_string_object l_NativeExecutionV3_typeText___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\ntype "};
static const lean_object* l_NativeExecutionV3_typeText___closed__2 = (const lean_object*)&l_NativeExecutionV3_typeText___closed__2_value;
LEAN_EXPORT lean_object* l_NativeExecutionV3_typeText(lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_typeText___boxed(lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "/root-types/"};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = ".expr"};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00NativeExecutionV3_types_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "constructor "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "/models/"};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "value "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inductive "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__2_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\nconstructors "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Unexpected model "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Expected theorem "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Expected model definition/inductive "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_NativeExecutionV3_types___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "DECLARATION_KIND_CHECK_PASS "};
static const lean_object* l_NativeExecutionV3_types___closed__0 = (const lean_object*)&l_NativeExecutionV3_types___closed__0_value;
static lean_once_cell_t l_NativeExecutionV3_types___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__1;
static lean_once_cell_t l_NativeExecutionV3_types___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__2;
static lean_once_cell_t l_NativeExecutionV3_types___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__3;
static const lean_string_object l_NativeExecutionV3_types___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " theorems; "};
static const lean_object* l_NativeExecutionV3_types___closed__4 = (const lean_object*)&l_NativeExecutionV3_types___closed__4_value;
static lean_once_cell_t l_NativeExecutionV3_types___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__5;
static lean_once_cell_t l_NativeExecutionV3_types___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__6;
static lean_once_cell_t l_NativeExecutionV3_types___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__7;
static lean_once_cell_t l_NativeExecutionV3_types___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__8;
static const lean_string_object l_NativeExecutionV3_types___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " definitions"};
static const lean_object* l_NativeExecutionV3_types___closed__9 = (const lean_object*)&l_NativeExecutionV3_types___closed__9_value;
static lean_once_cell_t l_NativeExecutionV3_types___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__10;
static lean_once_cell_t l_NativeExecutionV3_types___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__11;
static lean_once_cell_t l_NativeExecutionV3_types___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__12;
static lean_once_cell_t l_NativeExecutionV3_types___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__13;
static const lean_string_object l_NativeExecutionV3_types___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "ACTUAL_MODEL_CORE_EXPR_EXPORT_PASS "};
static const lean_object* l_NativeExecutionV3_types___closed__14 = (const lean_object*)&l_NativeExecutionV3_types___closed__14_value;
static lean_once_cell_t l_NativeExecutionV3_types___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__15;
static const lean_string_object l_NativeExecutionV3_types___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " models"};
static const lean_object* l_NativeExecutionV3_types___closed__16 = (const lean_object*)&l_NativeExecutionV3_types___closed__16_value;
static lean_once_cell_t l_NativeExecutionV3_types___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__17;
static const lean_string_object l_NativeExecutionV3_types___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "/AXIOM_REPORT.json"};
static const lean_object* l_NativeExecutionV3_types___closed__18 = (const lean_object*)&l_NativeExecutionV3_types___closed__18_value;
static const lean_string_object l_NativeExecutionV3_types___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ACTUAL_TYPE_AXIOM_REPORT_PASS "};
static const lean_object* l_NativeExecutionV3_types___closed__19 = (const lean_object*)&l_NativeExecutionV3_types___closed__19_value;
static lean_once_cell_t l_NativeExecutionV3_types___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__20;
static lean_once_cell_t l_NativeExecutionV3_types___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__21;
static lean_once_cell_t l_NativeExecutionV3_types___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__22;
static const lean_string_object l_NativeExecutionV3_types___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " roots"};
static const lean_object* l_NativeExecutionV3_types___closed__23 = (const lean_object*)&l_NativeExecutionV3_types___closed__23_value;
static lean_once_cell_t l_NativeExecutionV3_types___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_types___closed__24;
LEAN_EXPORT lean_object* l_NativeExecutionV3_types(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_types___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Changed type/levels "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Replayed root missing "};
static const lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00NativeExecutionV3_positive_spec__1(lean_object*, lean_object*);
static const lean_string_object l_NativeExecutionV3_positive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "POSITIVE_CLOSURE_READY "};
static const lean_object* l_NativeExecutionV3_positive___closed__0 = (const lean_object*)&l_NativeExecutionV3_positive___closed__0_value;
static const lean_string_object l_NativeExecutionV3_positive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " declarations"};
static const lean_object* l_NativeExecutionV3_positive___closed__1 = (const lean_object*)&l_NativeExecutionV3_positive___closed__1_value;
static const lean_string_object l_NativeExecutionV3_positive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "/kernel-roots.txt"};
static const lean_object* l_NativeExecutionV3_positive___closed__2 = (const lean_object*)&l_NativeExecutionV3_positive___closed__2_value;
static lean_once_cell_t l_NativeExecutionV3_positive___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_positive___closed__3;
static const lean_string_object l_NativeExecutionV3_positive___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "/kernel-closure.txt"};
static const lean_object* l_NativeExecutionV3_positive___closed__4 = (const lean_object*)&l_NativeExecutionV3_positive___closed__4_value;
static const lean_string_object l_NativeExecutionV3_positive___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "/kernel-axioms.txt"};
static const lean_object* l_NativeExecutionV3_positive___closed__5 = (const lean_object*)&l_NativeExecutionV3_positive___closed__5_value;
static const lean_string_object l_NativeExecutionV3_positive___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "EMPTY_KERNEL_REPLAY_PASS "};
static const lean_object* l_NativeExecutionV3_positive___closed__6 = (const lean_object*)&l_NativeExecutionV3_positive___closed__6_value;
static const lean_string_object l_NativeExecutionV3_positive___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " declarations; "};
static const lean_object* l_NativeExecutionV3_positive___closed__7 = (const lean_object*)&l_NativeExecutionV3_positive___closed__7_value;
static lean_once_cell_t l_NativeExecutionV3_positive___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_positive___closed__8;
static lean_once_cell_t l_NativeExecutionV3_positive___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_positive___closed__9;
static const lean_string_object l_NativeExecutionV3_positive___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " roots; trust level zero"};
static const lean_object* l_NativeExecutionV3_positive___closed__10 = (const lean_object*)&l_NativeExecutionV3_positive___closed__10_value;
LEAN_EXPORT lean_object* l_NativeExecutionV3_positive(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_positive___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_NativeExecutionV3_control___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "/control-"};
static const lean_object* l_NativeExecutionV3_control___closed__0 = (const lean_object*)&l_NativeExecutionV3_control___closed__0_value;
static const lean_string_object l_NativeExecutionV3_control___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "-roots.txt"};
static const lean_object* l_NativeExecutionV3_control___closed__1 = (const lean_object*)&l_NativeExecutionV3_control___closed__1_value;
static const lean_string_object l_NativeExecutionV3_control___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "-type-dependencies.txt"};
static const lean_object* l_NativeExecutionV3_control___closed__2 = (const lean_object*)&l_NativeExecutionV3_control___closed__2_value;
static const lean_string_object l_NativeExecutionV3_control___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "-axioms.txt"};
static const lean_object* l_NativeExecutionV3_control___closed__3 = (const lean_object*)&l_NativeExecutionV3_control___closed__3_value;
static const lean_string_object l_NativeExecutionV3_control___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "CORRUPTED_PROOF_REJECTED "};
static const lean_object* l_NativeExecutionV3_control___closed__4 = (const lean_object*)&l_NativeExecutionV3_control___closed__4_value;
static const lean_string_object l_NativeExecutionV3_control___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED "};
static const lean_object* l_NativeExecutionV3_control___closed__5 = (const lean_object*)&l_NativeExecutionV3_control___closed__5_value;
static const lean_string_object l_NativeExecutionV3_control___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Unexpected rejection reason: "};
static const lean_object* l_NativeExecutionV3_control___closed__6 = (const lean_object*)&l_NativeExecutionV3_control___closed__6_value;
static const lean_string_object l_NativeExecutionV3_control___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "EXPECTED_KERNEL_REJECTION: "};
static const lean_object* l_NativeExecutionV3_control___closed__7 = (const lean_object*)&l_NativeExecutionV3_control___closed__7_value;
static const lean_string_object l_NativeExecutionV3_control___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(kernel) declaration type mismatch"};
static const lean_object* l_NativeExecutionV3_control___closed__8 = (const lean_object*)&l_NativeExecutionV3_control___closed__8_value;
static const lean_string_object l_NativeExecutionV3_control___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "while replaying declaration '"};
static const lean_object* l_NativeExecutionV3_control___closed__9 = (const lean_object*)&l_NativeExecutionV3_control___closed__9_value;
static const lean_string_object l_NativeExecutionV3_control___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_NativeExecutionV3_control___closed__10 = (const lean_object*)&l_NativeExecutionV3_control___closed__10_value;
static const lean_string_object l_NativeExecutionV3_control___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_NativeExecutionV3_control___closed__11 = (const lean_object*)&l_NativeExecutionV3_control___closed__11_value;
static const lean_string_object l_NativeExecutionV3_control___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_NativeExecutionV3_control___closed__12 = (const lean_object*)&l_NativeExecutionV3_control___closed__12_value;
static const lean_string_object l_NativeExecutionV3_control___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_NativeExecutionV3_control___closed__13 = (const lean_object*)&l_NativeExecutionV3_control___closed__13_value;
static const lean_ctor_object l_NativeExecutionV3_control___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_control___closed__12_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_NativeExecutionV3_control___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_NativeExecutionV3_control___closed__14_value_aux_0),((lean_object*)&l_NativeExecutionV3_control___closed__13_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_NativeExecutionV3_control___closed__14 = (const lean_object*)&l_NativeExecutionV3_control___closed__14_value;
static lean_once_cell_t l_NativeExecutionV3_control___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_NativeExecutionV3_control___closed__15;
static const lean_string_object l_NativeExecutionV3_control___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Corruption changed expected type/levels"};
static const lean_object* l_NativeExecutionV3_control___closed__16 = (const lean_object*)&l_NativeExecutionV3_control___closed__16_value;
static const lean_ctor_object l_NativeExecutionV3_control___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_NativeExecutionV3_control___closed__16_value)}};
static const lean_object* l_NativeExecutionV3_control___closed__17 = (const lean_object*)&l_NativeExecutionV3_control___closed__17_value;
static const lean_string_object l_NativeExecutionV3_control___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Missing forged constructor"};
static const lean_object* l_NativeExecutionV3_control___closed__18 = (const lean_object*)&l_NativeExecutionV3_control___closed__18_value;
static const lean_ctor_object l_NativeExecutionV3_control___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_NativeExecutionV3_control___closed__18_value)}};
static const lean_object* l_NativeExecutionV3_control___closed__19 = (const lean_object*)&l_NativeExecutionV3_control___closed__19_value;
static const lean_string_object l_NativeExecutionV3_control___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "TYPE_CLOSURE_REPLAY_PASS "};
static const lean_object* l_NativeExecutionV3_control___closed__20 = (const lean_object*)&l_NativeExecutionV3_control___closed__20_value;
static const lean_string_object l_NativeExecutionV3_control___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " declarations; trust level zero"};
static const lean_object* l_NativeExecutionV3_control___closed__21 = (const lean_object*)&l_NativeExecutionV3_control___closed__21_value;
static const lean_string_object l_NativeExecutionV3_control___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Forged theorem accepted"};
static const lean_object* l_NativeExecutionV3_control___closed__22 = (const lean_object*)&l_NativeExecutionV3_control___closed__22_value;
static const lean_ctor_object l_NativeExecutionV3_control___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_NativeExecutionV3_control___closed__22_value)}};
static const lean_object* l_NativeExecutionV3_control___closed__23 = (const lean_object*)&l_NativeExecutionV3_control___closed__23_value;
static const lean_string_object l_NativeExecutionV3_control___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Unexpected self dependency"};
static const lean_object* l_NativeExecutionV3_control___closed__24 = (const lean_object*)&l_NativeExecutionV3_control___closed__24_value;
static const lean_ctor_object l_NativeExecutionV3_control___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_NativeExecutionV3_control___closed__24_value)}};
static const lean_object* l_NativeExecutionV3_control___closed__25 = (const lean_object*)&l_NativeExecutionV3_control___closed__25_value;
static const lean_string_object l_NativeExecutionV3_control___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Corruption control must select theorem"};
static const lean_object* l_NativeExecutionV3_control___closed__26 = (const lean_object*)&l_NativeExecutionV3_control___closed__26_value;
static const lean_ctor_object l_NativeExecutionV3_control___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_NativeExecutionV3_control___closed__26_value)}};
static const lean_object* l_NativeExecutionV3_control___closed__27 = (const lean_object*)&l_NativeExecutionV3_control___closed__27_value;
static const lean_string_object l_NativeExecutionV3_control___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Control index out of scope"};
static const lean_object* l_NativeExecutionV3_control___closed__28 = (const lean_object*)&l_NativeExecutionV3_control___closed__28_value;
static const lean_ctor_object l_NativeExecutionV3_control___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_NativeExecutionV3_control___closed__28_value)}};
static const lean_object* l_NativeExecutionV3_control___closed__29 = (const lean_object*)&l_NativeExecutionV3_control___closed__29_value;
static const lean_string_object l_NativeExecutionV3_control___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Control indices start at one"};
static const lean_object* l_NativeExecutionV3_control___closed__30 = (const lean_object*)&l_NativeExecutionV3_control___closed__30_value;
static const lean_ctor_object l_NativeExecutionV3_control___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_NativeExecutionV3_control___closed__30_value)}};
static const lean_object* l_NativeExecutionV3_control___closed__31 = (const lean_object*)&l_NativeExecutionV3_control___closed__31_value;
LEAN_EXPORT lean_object* l_NativeExecutionV3_control(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_control___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "NATIVE_MAX_MEMORY_BYTES 4194304000"};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_string_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "AssembledProgram"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_ctor_object l_main___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_NativeExecutionV3_theoremNames___closed__68_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__3_value_aux_0),((lean_object*)&l_main___closed__2_value),LEAN_SCALAR_PTR_LITERAL(138, 150, 138, 217, 68, 215, 217, 45)}};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static const lean_ctor_object l_main___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___closed__4 = (const lean_object*)&l_main___closed__4_value;
static const lean_array_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__4_value)}};
static const lean_object* l_main___closed__5 = (const lean_object*)&l_main___closed__5_value;
static const lean_array_object l_main___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__6 = (const lean_object*)&l_main___closed__6_value;
static const lean_string_object l_main___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "DATA_ONLY_IMPORT_COMPLETE_NOT_KERNEL_REPLAY"};
static const lean_object* l_main___closed__7 = (const lean_object*)&l_main___closed__7_value;
static const lean_string_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Expected types OUT | positive OUT | control INDEX OUT"};
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
static const lean_ctor_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_main___closed__8_value)}};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "types"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_string_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "positive"};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "control"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_string_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Invalid control index"};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_ctor_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_main___closed__13_value)}};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_NativeExecutionV3_setMaximumMemory___boxed(lean_object* v_max_3_, lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
size_t v_max_boxed_5_; lean_object* v_res_6_; 
v_max_boxed_5_ = lean_unbox_usize(v_max_3_);
lean_dec(v_max_3_);
v_res_6_ = lean_internal_set_max_memory(v_max_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_emit(lean_object* v_text_646_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_get_stdout();
lean_inc_ref(v___x_648_);
v___x_649_ = l_IO_FS_Stream_putStrLn(v___x_648_, v_text_646_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_flush_650_; lean_object* v___x_651_; 
lean_dec_ref_known(v___x_649_, 1);
v_flush_650_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_flush_650_);
lean_dec_ref(v___x_648_);
v___x_651_ = lean_apply_1(v_flush_650_, lean_box(0));
return v___x_651_;
}
else
{
lean_dec_ref(v___x_648_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_emit___boxed(lean_object* v_text_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_NativeExecutionV3_emit(v_text_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00NativeExecutionV3_collect_spec__0(lean_object* v_init_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
lean_object* v_k_657_; lean_object* v_l_658_; lean_object* v_r_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_k_657_ = lean_ctor_get(v_x_656_, 1);
v_l_658_ = lean_ctor_get(v_x_656_, 3);
v_r_659_ = lean_ctor_get(v_x_656_, 4);
v___x_660_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00NativeExecutionV3_collect_spec__0(v_init_655_, v_r_659_);
lean_inc(v_k_657_);
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v_k_657_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v_init_655_ = v___x_661_;
v_x_656_ = v_l_658_;
goto _start;
}
else
{
return v_init_655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00NativeExecutionV3_collect_spec__0___boxed(lean_object* v_init_663_, lean_object* v_x_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00NativeExecutionV3_collect_spec__0(v_init_663_, v_x_664_);
lean_dec(v_x_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_collect(lean_object* v_env_667_, lean_object* v_todo_668_, lean_object* v_seen_669_){
_start:
{
if (lean_obj_tag(v_todo_668_) == 0)
{
lean_object* v___x_670_; 
lean_dec_ref(v_env_667_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v_seen_669_);
return v___x_670_;
}
else
{
lean_object* v_head_671_; lean_object* v_tail_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_707_; 
v_head_671_ = lean_ctor_get(v_todo_668_, 0);
v_tail_672_ = lean_ctor_get(v_todo_668_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_todo_668_);
if (v_isSharedCheck_707_ == 0)
{
v___x_674_ = v_todo_668_;
v_isShared_675_ = v_isSharedCheck_707_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_tail_672_);
lean_inc(v_head_671_);
lean_dec(v_todo_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_707_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
uint8_t v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg(v_seen_669_, v_head_671_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_inc(v_head_671_);
lean_inc_ref(v_env_667_);
v___x_677_ = l_Lean_Environment_find_x3f(v_env_667_, v_head_671_, v___x_676_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_del_object(v___x_674_);
lean_dec(v_tail_672_);
lean_dec_ref(v_seen_669_);
lean_dec_ref(v_env_667_);
v___x_678_ = ((lean_object*)(l_NativeExecutionV3_collect___closed__0));
v___x_679_ = 1;
v___x_680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_671_, v___x_679_);
v___x_681_ = lean_string_append(v___x_678_, v___x_680_);
lean_dec_ref(v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
else
{
lean_object* v_val_683_; lean_object* v___y_685_; 
v_val_683_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_val_683_);
lean_dec_ref_known(v___x_677_, 1);
switch(lean_obj_tag(v_val_683_))
{
case 5:
{
lean_object* v_val_693_; lean_object* v_all_694_; lean_object* v_ctors_695_; lean_object* v___x_696_; 
lean_del_object(v___x_674_);
v_val_693_ = lean_ctor_get(v_val_683_, 0);
v_all_694_ = lean_ctor_get(v_val_693_, 3);
v_ctors_695_ = lean_ctor_get(v_val_693_, 4);
lean_inc(v_ctors_695_);
lean_inc(v_all_694_);
v___x_696_ = l_List_appendTR___redArg(v_all_694_, v_ctors_695_);
v___y_685_ = v___x_696_;
goto v___jp_684_;
}
case 6:
{
lean_object* v_val_697_; lean_object* v_induct_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v_val_697_ = lean_ctor_get(v_val_683_, 0);
v_induct_698_ = lean_ctor_get(v_val_697_, 1);
v___x_699_ = lean_box(0);
lean_inc(v_induct_698_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___x_699_);
lean_ctor_set(v___x_674_, 0, v_induct_698_);
v___x_701_ = v___x_674_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_induct_698_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v___y_685_ = v___x_701_;
goto v___jp_684_;
}
}
case 7:
{
lean_object* v_val_703_; lean_object* v_all_704_; 
lean_del_object(v___x_674_);
v_val_703_ = lean_ctor_get(v_val_683_, 0);
v_all_704_ = lean_ctor_get(v_val_703_, 1);
lean_inc(v_all_704_);
v___y_685_ = v_all_704_;
goto v___jp_684_;
}
default: 
{
lean_object* v___x_705_; 
lean_del_object(v___x_674_);
v___x_705_ = lean_box(0);
v___y_685_ = v___x_705_;
goto v___jp_684_;
}
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_inc(v_val_683_);
v___x_686_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v_val_683_);
v___x_687_ = lean_box(0);
v___x_688_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00NativeExecutionV3_collect_spec__0(v___x_687_, v___x_686_);
lean_dec(v___x_686_);
v___x_689_ = l_List_appendTR___redArg(v___y_685_, v___x_688_);
v___x_690_ = l_List_appendTR___redArg(v___x_689_, v_tail_672_);
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_seen_669_, v_head_671_, v_val_683_);
v_todo_668_ = v___x_690_;
v_seen_669_ = v___x_691_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_674_);
lean_dec(v_head_671_);
v_todo_668_ = v_tail_672_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_NativeExecutionV3_collected___closed__0(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = lean_box(0);
v___x_709_ = lean_unsigned_to_nat(16u);
v___x_710_ = lean_mk_array(v___x_709_, v___x_708_);
return v___x_710_;
}
}
static lean_object* _init_l_NativeExecutionV3_collected___closed__1(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_obj_once(&l_NativeExecutionV3_collected___closed__0, &l_NativeExecutionV3_collected___closed__0_once, _init_l_NativeExecutionV3_collected___closed__0);
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v___x_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_collected(lean_object* v_env_714_, lean_object* v_names_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_obj_once(&l_NativeExecutionV3_collected___closed__1, &l_NativeExecutionV3_collected___closed__1_once, _init_l_NativeExecutionV3_collected___closed__1);
v___x_718_ = l_NativeExecutionV3_collect(v_env_714_, v_names_715_, v___x_717_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_727_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_727_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_727_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 18);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_726_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_718_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_718_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 0);
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_collected___boxed(lean_object* v_env_736_, lean_object* v_names_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_NativeExecutionV3_collected(v_env_736_, v_names_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg(lean_object* v_as_x27_764_, lean_object* v_b_765_){
_start:
{
if (lean_obj_tag(v_as_x27_764_) == 0)
{
lean_object* v___x_767_; 
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_b_765_);
return v___x_767_;
}
else
{
lean_object* v_head_768_; lean_object* v_tail_769_; lean_object* v_fst_770_; lean_object* v_snd_771_; lean_object* v___x_772_; uint8_t v___y_774_; uint8_t v___y_782_; uint8_t v___x_792_; 
v_head_768_ = lean_ctor_get(v_as_x27_764_, 0);
v_tail_769_ = lean_ctor_get(v_as_x27_764_, 1);
v_fst_770_ = lean_ctor_get(v_head_768_, 0);
v_snd_771_ = lean_ctor_get(v_head_768_, 1);
v___x_772_ = lean_box(0);
v___x_792_ = l_Lean_ConstantInfo_isUnsafe(v_snd_771_);
if (v___x_792_ == 0)
{
uint8_t v___x_793_; 
v___x_793_ = l_Lean_ConstantInfo_isPartial(v_snd_771_);
v___y_782_ = v___x_793_;
goto v___jp_781_;
}
else
{
v___y_782_ = v___x_792_;
goto v___jp_781_;
}
v___jp_773_:
{
if (v___y_774_ == 0)
{
v_as_x27_764_ = v_tail_769_;
v_b_765_ = v___x_772_;
goto _start;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_776_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__0));
lean_inc(v_fst_770_);
v___x_777_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_770_, v___y_774_);
v___x_778_ = lean_string_append(v___x_776_, v___x_777_);
lean_dec_ref(v___x_777_);
v___x_779_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
v___jp_781_:
{
if (v___y_782_ == 0)
{
uint8_t v___x_783_; 
v___x_783_ = l_Lean_ConstantInfo_isAxiom(v_snd_771_);
if (v___x_783_ == 0)
{
v___y_774_ = v___x_783_;
goto v___jp_773_;
}
else
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__11));
v___x_785_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(v_fst_770_, v___x_784_);
if (v___x_785_ == 0)
{
v___y_774_ = v___x_783_;
goto v___jp_773_;
}
else
{
v_as_x27_764_ = v_tail_769_;
v_b_765_ = v___x_772_;
goto _start;
}
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_787_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___closed__12));
lean_inc(v_fst_770_);
v___x_788_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_770_, v___y_782_);
v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
lean_dec_ref(v___x_788_);
v___x_790_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg___boxed(lean_object* v_as_x27_794_, lean_object* v_b_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg(v_as_x27_794_, v_b_795_);
lean_dec(v_as_x27_794_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_checkSafety(lean_object* v_cs_798_){
_start:
{
lean_object* v___y_801_; lean_object* v_buckets_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_buckets_812_ = lean_ctor_get(v_cs_798_, 1);
v___x_813_ = lean_box(0);
v___x_814_ = lean_array_get_size(v_buckets_812_);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_nat_dec_lt(v___x_815_, v___x_814_);
if (v___x_816_ == 0)
{
v___y_801_ = v___x_813_;
goto v___jp_800_;
}
else
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_usize_of_nat(v___x_814_);
v___x_818_ = ((size_t)0ULL);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_buckets_812_, v___x_817_, v___x_818_, v___x_813_);
v___y_801_ = v___x_819_;
goto v___jp_800_;
}
v___jp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_box(0);
v___x_803_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg(v___y_801_, v___x_802_);
lean_dec(v___y_801_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_810_; 
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_803_, 0);
lean_dec(v_unused_811_);
v___x_805_ = v___x_803_;
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
else
{
lean_dec(v___x_803_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_810_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_802_);
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_802_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
else
{
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_checkSafety___boxed(lean_object* v_cs_820_, lean_object* v_a_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_NativeExecutionV3_checkSafety(v_cs_820_);
lean_dec_ref(v_cs_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0(lean_object* v_as_823_, lean_object* v_as_x27_824_, lean_object* v_b_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___redArg(v_as_x27_824_, v_b_825_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0___boxed(lean_object* v_as_829_, lean_object* v_as_x27_830_, lean_object* v_b_831_, lean_object* v_a_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_checkSafety_spec__0(v_as_829_, v_as_x27_830_, v_b_831_, v_a_832_);
lean_dec(v_as_x27_830_);
lean_dec(v_as_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00NativeExecutionV3_sortedNames_spec__0(lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
if (lean_obj_tag(v_a_835_) == 0)
{
lean_object* v___x_837_; 
v___x_837_ = l_List_reverse___redArg(v_a_836_);
return v___x_837_;
}
else
{
lean_object* v_head_838_; lean_object* v_tail_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_850_; 
v_head_838_ = lean_ctor_get(v_a_835_, 0);
v_tail_839_ = lean_ctor_get(v_a_835_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v_a_835_);
if (v_isSharedCheck_850_ == 0)
{
v___x_841_ = v_a_835_;
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_tail_839_);
lean_inc(v_head_838_);
lean_dec(v_a_835_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_850_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_fst_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v_fst_843_ = lean_ctor_get(v_head_838_, 0);
lean_inc(v_fst_843_);
lean_dec(v_head_838_);
v___x_844_ = 1;
v___x_845_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_843_, v___x_844_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 1, v_a_836_);
lean_ctor_set(v___x_841_, 0, v___x_845_);
v___x_847_ = v___x_841_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_a_836_);
v___x_847_ = v_reuseFailAlloc_849_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
v_a_835_ = v_tail_839_;
v_a_836_ = v___x_847_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_sortedNames(lean_object* v_cs_852_){
_start:
{
lean_object* v_buckets_853_; lean_object* v___f_854_; lean_object* v___y_856_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v_buckets_853_ = lean_ctor_get(v_cs_852_, 1);
v___f_854_ = ((lean_object*)(l_NativeExecutionV3_sortedNames___closed__0));
v___x_860_ = lean_box(0);
v___x_861_ = lean_array_get_size(v_buckets_853_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_nat_dec_lt(v___x_862_, v___x_861_);
if (v___x_863_ == 0)
{
v___y_856_ = v___x_860_;
goto v___jp_855_;
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_usize_of_nat(v___x_861_);
v___x_865_ = ((size_t)0ULL);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_buckets_853_, v___x_864_, v___x_865_, v___x_860_);
v___y_856_ = v___x_866_;
goto v___jp_855_;
}
v___jp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_box(0);
v___x_858_ = l_List_mapTR_loop___at___00NativeExecutionV3_sortedNames_spec__0(v___y_856_, v___x_857_);
v___x_859_ = l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(v___x_858_, v___f_854_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_sortedNames___boxed(lean_object* v_cs_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_NativeExecutionV3_sortedNames(v_cs_867_);
lean_dec_ref(v_cs_867_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00NativeExecutionV3_axiomNames_spec__0(lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
if (lean_obj_tag(v_a_869_) == 0)
{
lean_object* v___x_871_; 
v___x_871_ = lean_array_to_list(v_a_870_);
return v___x_871_;
}
else
{
lean_object* v_head_872_; lean_object* v_tail_873_; lean_object* v_fst_874_; lean_object* v_snd_875_; uint8_t v___x_876_; 
v_head_872_ = lean_ctor_get(v_a_869_, 0);
lean_inc(v_head_872_);
v_tail_873_ = lean_ctor_get(v_a_869_, 1);
lean_inc(v_tail_873_);
lean_dec_ref_known(v_a_869_, 2);
v_fst_874_ = lean_ctor_get(v_head_872_, 0);
lean_inc(v_fst_874_);
v_snd_875_ = lean_ctor_get(v_head_872_, 1);
lean_inc(v_snd_875_);
lean_dec(v_head_872_);
v___x_876_ = l_Lean_ConstantInfo_isAxiom(v_snd_875_);
lean_dec(v_snd_875_);
if (v___x_876_ == 0)
{
lean_dec(v_fst_874_);
v_a_869_ = v_tail_873_;
goto _start;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_874_, v___x_876_);
v___x_879_ = lean_array_push(v_a_870_, v___x_878_);
v_a_869_ = v_tail_873_;
v_a_870_ = v___x_879_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_axiomNames(lean_object* v_cs_883_){
_start:
{
lean_object* v_buckets_884_; lean_object* v___f_885_; lean_object* v___y_887_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_buckets_884_ = lean_ctor_get(v_cs_883_, 1);
v___f_885_ = ((lean_object*)(l_NativeExecutionV3_sortedNames___closed__0));
v___x_891_ = lean_box(0);
v___x_892_ = lean_array_get_size(v_buckets_884_);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_nat_dec_lt(v___x_893_, v___x_892_);
if (v___x_894_ == 0)
{
v___y_887_ = v___x_891_;
goto v___jp_886_;
}
else
{
size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_usize_of_nat(v___x_892_);
v___x_896_ = ((size_t)0ULL);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Kernel_Environment_replay_spec__2(v_buckets_884_, v___x_895_, v___x_896_, v___x_891_);
v___y_887_ = v___x_897_;
goto v___jp_886_;
}
v___jp_886_:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = ((lean_object*)(l_NativeExecutionV3_axiomNames___closed__0));
v___x_889_ = l_List_filterMapTR_go___at___00NativeExecutionV3_axiomNames_spec__0(v___y_887_, v___x_888_);
v___x_890_ = l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(v___x_889_, v___f_885_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_axiomNames___boxed(lean_object* v_cs_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_NativeExecutionV3_axiomNames(v_cs_898_);
lean_dec_ref(v_cs_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_writeLines(lean_object* v_path_901_, lean_object* v_names_902_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = ((lean_object*)(l_NativeExecutionV3_writeLines___closed__0));
v___x_905_ = l_String_intercalate(v___x_904_, v_names_902_);
v___x_906_ = lean_string_append(v___x_905_, v___x_904_);
v___x_907_ = l_IO_FS_writeFile(v_path_901_, v___x_906_);
lean_dec_ref(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_writeLines___boxed(lean_object* v_path_908_, lean_object* v_names_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_NativeExecutionV3_writeLines(v_path_908_, v_names_909_);
lean_dec_ref(v_path_908_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_jsonFile(lean_object* v_path_912_, lean_object* v_j_913_){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_915_ = lean_unsigned_to_nat(80u);
v___x_916_ = l_Lean_Json_pretty(v_j_913_, v___x_915_);
v___x_917_ = ((lean_object*)(l_NativeExecutionV3_writeLines___closed__0));
v___x_918_ = lean_string_append(v___x_916_, v___x_917_);
v___x_919_ = l_IO_FS_writeFile(v_path_912_, v___x_918_);
lean_dec_ref(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_jsonFile___boxed(lean_object* v_path_920_, lean_object* v_j_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_NativeExecutionV3_jsonFile(v_path_920_, v_j_921_);
lean_dec_ref(v_path_920_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_info(lean_object* v_env_925_, lean_object* v_n_926_){
_start:
{
uint8_t v___x_928_; lean_object* v___x_929_; 
v___x_928_ = 0;
lean_inc(v_n_926_);
v___x_929_ = l_Lean_Environment_find_x3f(v_env_925_, v_n_926_, v___x_928_);
if (lean_obj_tag(v___x_929_) == 1)
{
lean_object* v_val_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_n_926_);
v_val_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_val_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 0);
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_val_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
else
{
lean_object* v___x_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v___x_929_);
v___x_938_ = ((lean_object*)(l_NativeExecutionV3_info___closed__0));
v___x_939_ = 1;
v___x_940_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_926_, v___x_939_);
v___x_941_ = lean_string_append(v___x_938_, v___x_940_);
lean_dec_ref(v___x_940_);
v___x_942_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_info___boxed(lean_object* v_env_944_, lean_object* v_n_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_NativeExecutionV3_info(v_env_944_, v_n_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_typeText(lean_object* v_ci_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_952_ = ((lean_object*)(l_NativeExecutionV3_typeText___closed__0));
v___x_953_ = l_Lean_ConstantInfo_name(v_ci_951_);
v___x_954_ = 1;
v___x_955_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_953_, v___x_954_);
v___x_956_ = lean_string_append(v___x_952_, v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = ((lean_object*)(l_NativeExecutionV3_typeText___closed__1));
v___x_958_ = lean_string_append(v___x_956_, v___x_957_);
v___x_959_ = l_Lean_ConstantInfo_levelParams(v_ci_951_);
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = l_List_repr___at___00Lean_Environment_dbgFormatAsyncState_spec__2___redArg(v___x_959_);
v___x_962_ = lean_unsigned_to_nat(120u);
v___x_963_ = l_Std_Format_pretty(v___x_961_, v___x_962_, v___x_960_, v___x_960_);
v___x_964_ = lean_string_append(v___x_958_, v___x_963_);
lean_dec_ref(v___x_963_);
v___x_965_ = ((lean_object*)(l_NativeExecutionV3_typeText___closed__2));
v___x_966_ = lean_string_append(v___x_964_, v___x_965_);
v___x_967_ = l_Lean_ConstantInfo_type(v_ci_951_);
v___x_968_ = l_Lean_instReprExpr_repr(v___x_967_, v___x_960_);
v___x_969_ = l_Std_Format_pretty(v___x_968_, v___x_962_, v___x_960_, v___x_960_);
v___x_970_ = lean_string_append(v___x_966_, v___x_969_);
lean_dec_ref(v___x_969_);
v___x_971_ = ((lean_object*)(l_NativeExecutionV3_writeLines___closed__0));
v___x_972_ = lean_string_append(v___x_970_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_typeText___boxed(lean_object* v_ci_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_NativeExecutionV3_typeText(v_ci_973_);
lean_dec_ref(v_ci_973_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg(lean_object* v_env_977_, lean_object* v_out_978_, lean_object* v_as_x27_979_, lean_object* v_b_980_){
_start:
{
if (lean_obj_tag(v_as_x27_979_) == 0)
{
lean_object* v___x_982_; 
lean_dec_ref(v_out_978_);
lean_dec_ref(v_env_977_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v_b_980_);
return v___x_982_;
}
else
{
lean_object* v_head_983_; lean_object* v_tail_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_987_; 
v_head_983_ = lean_ctor_get(v_as_x27_979_, 0);
v_tail_984_ = lean_ctor_get(v_as_x27_979_, 1);
v_fst_985_ = lean_ctor_get(v_head_983_, 0);
v_snd_986_ = lean_ctor_get(v_head_983_, 1);
lean_inc(v_fst_985_);
lean_inc_ref(v_env_977_);
v___x_987_ = l_NativeExecutionV3_info(v_env_977_, v_fst_985_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_987_, 1);
v___x_989_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___closed__0));
lean_inc_ref(v_out_978_);
v___x_990_ = lean_string_append(v_out_978_, v___x_989_);
v___x_991_ = lean_unsigned_to_nat(1u);
v___x_992_ = lean_nat_add(v_snd_986_, v___x_991_);
v___x_993_ = l_Nat_reprFast(v___x_992_);
v___x_994_ = lean_string_append(v___x_990_, v___x_993_);
lean_dec_ref(v___x_993_);
v___x_995_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___closed__1));
v___x_996_ = lean_string_append(v___x_994_, v___x_995_);
v___x_997_ = l_NativeExecutionV3_typeText(v_a_988_);
lean_dec(v_a_988_);
v___x_998_ = l_IO_FS_writeFile(v___x_996_, v___x_997_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v___x_996_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_999_; 
lean_dec_ref_known(v___x_998_, 1);
v___x_999_ = lean_box(0);
v_as_x27_979_ = v_tail_984_;
v_b_980_ = v___x_999_;
goto _start;
}
else
{
lean_dec_ref(v_out_978_);
lean_dec_ref(v_env_977_);
return v___x_998_;
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v_out_978_);
lean_dec_ref(v_env_977_);
v_a_1001_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_987_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_987_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___boxed(lean_object* v_env_1009_, lean_object* v_out_1010_, lean_object* v_as_x27_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg(v_env_1009_, v_out_1010_, v_as_x27_1011_, v_b_1012_);
lean_dec(v_as_x27_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00NativeExecutionV3_types_spec__5(lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
if (lean_obj_tag(v_a_1015_) == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = l_List_reverse___redArg(v_a_1016_);
return v___x_1017_;
}
else
{
lean_object* v_head_1018_; lean_object* v_tail_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1028_; 
v_head_1018_ = lean_ctor_get(v_a_1015_, 0);
v_tail_1019_ = lean_ctor_get(v_a_1015_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_a_1015_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1021_ = v_a_1015_;
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_tail_1019_);
lean_inc(v_head_1018_);
lean_dec(v_a_1015_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1028_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_head_1018_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v_a_1016_);
lean_ctor_set(v___x_1021_, 0, v___x_1023_);
v___x_1025_ = v___x_1021_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_a_1016_);
v___x_1025_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
v_a_1015_ = v_tail_1019_;
v_a_1016_ = v___x_1025_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6___redArg(lean_object* v_env_1029_, lean_object* v_as_x27_1030_, lean_object* v_b_1031_){
_start:
{
if (lean_obj_tag(v_as_x27_1030_) == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v_env_1029_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_b_1031_);
return v___x_1033_;
}
else
{
lean_object* v_head_1034_; lean_object* v_tail_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v_head_1034_ = lean_ctor_get(v_as_x27_1030_, 0);
v_tail_1035_ = lean_ctor_get(v_as_x27_1030_, 1);
v___x_1036_ = lean_box(0);
lean_inc(v_head_1034_);
v___x_1037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_head_1034_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
lean_inc_ref(v_env_1029_);
v___x_1038_ = l_NativeExecutionV3_collected(v_env_1029_, v___x_1037_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = l_NativeExecutionV3_checkSafety(v_a_1039_);
if (lean_obj_tag(v___x_1040_) == 0)
{
uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref_known(v___x_1040_, 1);
v___x_1041_ = 1;
lean_inc(v_head_1034_);
v___x_1042_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1034_, v___x_1041_);
v___x_1043_ = l_NativeExecutionV3_axiomNames(v_a_1039_);
lean_dec(v_a_1039_);
v___x_1044_ = l_List_mapTR_loop___at___00NativeExecutionV3_types_spec__5(v___x_1043_, v___x_1036_);
v___x_1045_ = lean_array_mk(v___x_1044_);
v___x_1046_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1042_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v___x_1036_);
v___x_1049_ = l_List_appendTR___redArg(v_b_1031_, v___x_1048_);
v_as_x27_1030_ = v_tail_1035_;
v_b_1031_ = v___x_1049_;
goto _start;
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec(v_a_1039_);
lean_dec(v_b_1031_);
lean_dec_ref(v_env_1029_);
v_a_1051_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1040_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1040_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_b_1031_);
lean_dec_ref(v_env_1029_);
v_a_1059_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1038_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1038_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6___redArg___boxed(lean_object* v_env_1067_, lean_object* v_as_x27_1068_, lean_object* v_b_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6___redArg(v_env_1067_, v_as_x27_1068_, v_b_1069_);
lean_dec(v_as_x27_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg(lean_object* v_env_1073_, lean_object* v_as_x27_1074_, lean_object* v_b_1075_){
_start:
{
if (lean_obj_tag(v_as_x27_1074_) == 0)
{
lean_object* v___x_1077_; 
lean_dec_ref(v_env_1073_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_b_1075_);
return v___x_1077_;
}
else
{
lean_object* v_head_1078_; lean_object* v_tail_1079_; lean_object* v___x_1080_; 
v_head_1078_ = lean_ctor_get(v_as_x27_1074_, 0);
v_tail_1079_ = lean_ctor_get(v_as_x27_1074_, 1);
lean_inc(v_head_1078_);
lean_inc_ref(v_env_1073_);
v___x_1080_ = l_NativeExecutionV3_info(v_env_1073_, v_head_1078_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg___closed__0));
v___x_1083_ = lean_string_append(v_b_1075_, v___x_1082_);
v___x_1084_ = l_NativeExecutionV3_typeText(v_a_1081_);
lean_dec(v_a_1081_);
v___x_1085_ = lean_string_append(v___x_1083_, v___x_1084_);
lean_dec_ref(v___x_1084_);
v_as_x27_1074_ = v_tail_1079_;
v_b_1075_ = v___x_1085_;
goto _start;
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_b_1075_);
lean_dec_ref(v_env_1073_);
v_a_1087_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1080_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1080_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg___boxed(lean_object* v_env_1095_, lean_object* v_as_x27_1096_, lean_object* v_b_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg(v_env_1095_, v_as_x27_1096_, v_b_1097_);
lean_dec(v_as_x27_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg(lean_object* v_env_1105_, lean_object* v_out_1106_, lean_object* v_as_x27_1107_, lean_object* v_b_1108_){
_start:
{
if (lean_obj_tag(v_as_x27_1107_) == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref(v_out_1106_);
lean_dec_ref(v_env_1105_);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v_b_1108_);
return v___x_1110_;
}
else
{
lean_object* v_head_1111_; lean_object* v_tail_1112_; lean_object* v_fst_1113_; lean_object* v_snd_1114_; lean_object* v___x_1115_; 
v_head_1111_ = lean_ctor_get(v_as_x27_1107_, 0);
v_tail_1112_ = lean_ctor_get(v_as_x27_1107_, 1);
v_fst_1113_ = lean_ctor_get(v_head_1111_, 0);
v_snd_1114_ = lean_ctor_get(v_head_1111_, 1);
lean_inc(v_fst_1113_);
lean_inc_ref(v_env_1105_);
v___x_1115_ = l_NativeExecutionV3_info(v_env_1105_, v_fst_1113_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1179_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1179_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1179_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v_tail_1122_; 
v___x_1120_ = lean_box(0);
switch(lean_obj_tag(v_a_1116_))
{
case 1:
{
lean_object* v_val_1135_; lean_object* v_value_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_del_object(v___x_1118_);
v_val_1135_ = lean_ctor_get(v_a_1116_, 0);
v_value_1136_ = lean_ctor_get(v_val_1135_, 1);
v___x_1137_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__1));
v___x_1138_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_value_1136_);
v___x_1139_ = l_Lean_instReprExpr_repr(v_value_1136_, v___x_1138_);
v___x_1140_ = lean_unsigned_to_nat(120u);
v___x_1141_ = l_Std_Format_pretty(v___x_1139_, v___x_1140_, v___x_1138_, v___x_1138_);
v___x_1142_ = lean_string_append(v___x_1137_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1143_ = ((lean_object*)(l_NativeExecutionV3_writeLines___closed__0));
v___x_1144_ = lean_string_append(v___x_1142_, v___x_1143_);
v_tail_1122_ = v___x_1144_;
goto v___jp_1121_;
}
case 5:
{
lean_object* v_val_1145_; lean_object* v_all_1146_; lean_object* v_ctors_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_del_object(v___x_1118_);
v_val_1145_ = lean_ctor_get(v_a_1116_, 0);
v_all_1146_ = lean_ctor_get(v_val_1145_, 3);
v_ctors_1147_ = lean_ctor_get(v_val_1145_, 4);
v___x_1148_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__2));
v___x_1149_ = lean_unsigned_to_nat(0u);
lean_inc(v_all_1146_);
v___x_1150_ = l_List_repr___at___00Lean_Environment_dbgFormatAsyncState_spec__2___redArg(v_all_1146_);
v___x_1151_ = lean_unsigned_to_nat(120u);
v___x_1152_ = l_Std_Format_pretty(v___x_1150_, v___x_1151_, v___x_1149_, v___x_1149_);
v___x_1153_ = lean_string_append(v___x_1148_, v___x_1152_);
lean_dec_ref(v___x_1152_);
v___x_1154_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__3));
v___x_1155_ = lean_string_append(v___x_1153_, v___x_1154_);
lean_inc(v_ctors_1147_);
v___x_1156_ = l_List_repr___at___00Lean_Environment_dbgFormatAsyncState_spec__2___redArg(v_ctors_1147_);
v___x_1157_ = l_Std_Format_pretty(v___x_1156_, v___x_1151_, v___x_1149_, v___x_1149_);
v___x_1158_ = lean_string_append(v___x_1155_, v___x_1157_);
lean_dec_ref(v___x_1157_);
v___x_1159_ = ((lean_object*)(l_NativeExecutionV3_writeLines___closed__0));
v___x_1160_ = lean_string_append(v___x_1158_, v___x_1159_);
lean_inc_ref(v_env_1105_);
v___x_1161_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg(v_env_1105_, v_ctors_1147_, v___x_1160_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v_tail_1122_ = v_a_1162_;
goto v___jp_1121_;
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref_known(v_a_1116_, 1);
lean_dec_ref(v_out_1106_);
lean_dec_ref(v_env_1105_);
v_a_1163_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1161_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1161_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
default: 
{
lean_object* v___x_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
lean_dec(v_a_1116_);
lean_dec_ref(v_out_1106_);
lean_dec_ref(v_env_1105_);
v___x_1171_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__4));
v___x_1172_ = 1;
lean_inc(v_fst_1113_);
v___x_1173_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_1113_, v___x_1172_);
v___x_1174_ = lean_string_append(v___x_1171_, v___x_1173_);
lean_dec_ref(v___x_1173_);
v___x_1175_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v___x_1175_);
v___x_1177_ = v___x_1118_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
v___jp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1123_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___closed__0));
lean_inc_ref(v_out_1106_);
v___x_1124_ = lean_string_append(v_out_1106_, v___x_1123_);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_add(v_snd_1114_, v___x_1125_);
v___x_1127_ = l_Nat_reprFast(v___x_1126_);
v___x_1128_ = lean_string_append(v___x_1124_, v___x_1127_);
lean_dec_ref(v___x_1127_);
v___x_1129_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg___closed__1));
v___x_1130_ = lean_string_append(v___x_1128_, v___x_1129_);
v___x_1131_ = l_NativeExecutionV3_typeText(v_a_1116_);
lean_dec(v_a_1116_);
v___x_1132_ = lean_string_append(v___x_1131_, v_tail_1122_);
lean_dec_ref(v_tail_1122_);
v___x_1133_ = l_IO_FS_writeFile(v___x_1130_, v___x_1132_);
lean_dec_ref(v___x_1132_);
lean_dec_ref(v___x_1130_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_dec_ref_known(v___x_1133_, 1);
v_as_x27_1107_ = v_tail_1112_;
v_b_1108_ = v___x_1120_;
goto _start;
}
else
{
lean_dec_ref(v_out_1106_);
lean_dec_ref(v_env_1105_);
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_out_1106_);
lean_dec_ref(v_env_1105_);
v_a_1180_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1115_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1115_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg___boxed(lean_object* v_env_1188_, lean_object* v_out_1189_, lean_object* v_as_x27_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg(v_env_1188_, v_out_1189_, v_as_x27_1190_, v_b_1191_);
lean_dec(v_as_x27_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg(lean_object* v_env_1195_, lean_object* v_as_x27_1196_, lean_object* v_b_1197_){
_start:
{
if (lean_obj_tag(v_as_x27_1196_) == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v_env_1195_);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v_b_1197_);
return v___x_1199_;
}
else
{
lean_object* v_head_1200_; lean_object* v_tail_1201_; lean_object* v___x_1202_; 
v_head_1200_ = lean_ctor_get(v_as_x27_1196_, 0);
v_tail_1201_ = lean_ctor_get(v_as_x27_1196_, 1);
lean_inc(v_head_1200_);
lean_inc_ref(v_env_1195_);
v___x_1202_ = l_NativeExecutionV3_info(v_env_1195_, v_head_1200_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1218_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1218_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1218_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
uint8_t v___x_1207_; 
v___x_1207_ = l_Lean_ConstantInfo_isTheorem(v_a_1203_);
lean_dec(v_a_1203_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; uint8_t v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_dec_ref(v_env_1195_);
v___x_1208_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg___closed__0));
v___x_1209_ = 1;
lean_inc(v_head_1200_);
v___x_1210_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1200_, v___x_1209_);
v___x_1211_ = lean_string_append(v___x_1208_, v___x_1210_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 1);
lean_ctor_set(v___x_1205_, 0, v___x_1212_);
v___x_1214_ = v___x_1205_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
else
{
lean_object* v___x_1216_; 
lean_del_object(v___x_1205_);
v___x_1216_ = lean_box(0);
v_as_x27_1196_ = v_tail_1201_;
v_b_1197_ = v___x_1216_;
goto _start;
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v_env_1195_);
v_a_1219_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1202_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1202_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg___boxed(lean_object* v_env_1227_, lean_object* v_as_x27_1228_, lean_object* v_b_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg(v_env_1227_, v_as_x27_1228_, v_b_1229_);
lean_dec(v_as_x27_1228_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg(lean_object* v_env_1233_, lean_object* v_as_x27_1234_, lean_object* v_b_1235_){
_start:
{
if (lean_obj_tag(v_as_x27_1234_) == 0)
{
lean_object* v___x_1237_; 
lean_dec_ref(v_env_1233_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_b_1235_);
return v___x_1237_;
}
else
{
lean_object* v_head_1238_; lean_object* v_tail_1239_; lean_object* v___x_1240_; 
v_head_1238_ = lean_ctor_get(v_as_x27_1234_, 0);
v_tail_1239_ = lean_ctor_get(v_as_x27_1234_, 1);
lean_inc(v_head_1238_);
lean_inc_ref(v_env_1233_);
v___x_1240_ = l_NativeExecutionV3_info(v_env_1233_, v_head_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1256_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1256_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1256_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; 
v___x_1245_ = lean_box(0);
switch(lean_obj_tag(v_a_1241_))
{
case 1:
{
lean_dec_ref_known(v_a_1241_, 1);
lean_del_object(v___x_1243_);
v_as_x27_1234_ = v_tail_1239_;
v_b_1235_ = v___x_1245_;
goto _start;
}
case 5:
{
lean_dec_ref_known(v_a_1241_, 1);
lean_del_object(v___x_1243_);
v_as_x27_1234_ = v_tail_1239_;
v_b_1235_ = v___x_1245_;
goto _start;
}
default: 
{
lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_dec(v_a_1241_);
lean_dec_ref(v_env_1233_);
v___x_1248_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg___closed__0));
v___x_1249_ = 1;
lean_inc(v_head_1238_);
v___x_1250_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1238_, v___x_1249_);
v___x_1251_ = lean_string_append(v___x_1248_, v___x_1250_);
lean_dec_ref(v___x_1250_);
v___x_1252_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 1);
lean_ctor_set(v___x_1243_, 0, v___x_1252_);
v___x_1254_ = v___x_1243_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec_ref(v_env_1233_);
v_a_1257_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1240_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1240_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg___boxed(lean_object* v_env_1265_, lean_object* v_as_x27_1266_, lean_object* v_b_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg(v_env_1265_, v_as_x27_1266_, v_b_1267_);
lean_dec(v_as_x27_1266_);
return v_res_1269_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__1(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_NativeExecutionV3_theoremNames));
v___x_1272_ = l_List_lengthTR___redArg(v___x_1271_);
return v___x_1272_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__2(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_obj_once(&l_NativeExecutionV3_types___closed__1, &l_NativeExecutionV3_types___closed__1_once, _init_l_NativeExecutionV3_types___closed__1);
v___x_1274_ = l_Nat_reprFast(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__3(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = lean_obj_once(&l_NativeExecutionV3_types___closed__2, &l_NativeExecutionV3_types___closed__2_once, _init_l_NativeExecutionV3_types___closed__2);
v___x_1276_ = ((lean_object*)(l_NativeExecutionV3_types___closed__0));
v___x_1277_ = lean_string_append(v___x_1276_, v___x_1275_);
return v___x_1277_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__5(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((lean_object*)(l_NativeExecutionV3_types___closed__4));
v___x_1280_ = lean_obj_once(&l_NativeExecutionV3_types___closed__3, &l_NativeExecutionV3_types___closed__3_once, _init_l_NativeExecutionV3_types___closed__3);
v___x_1281_ = lean_string_append(v___x_1280_, v___x_1279_);
return v___x_1281_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__6(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_NativeExecutionV3_modelNames));
v___x_1283_ = l_List_lengthTR___redArg(v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__7(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_obj_once(&l_NativeExecutionV3_types___closed__6, &l_NativeExecutionV3_types___closed__6_once, _init_l_NativeExecutionV3_types___closed__6);
v___x_1285_ = l_Nat_reprFast(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__8(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_obj_once(&l_NativeExecutionV3_types___closed__7, &l_NativeExecutionV3_types___closed__7_once, _init_l_NativeExecutionV3_types___closed__7);
v___x_1287_ = lean_obj_once(&l_NativeExecutionV3_types___closed__5, &l_NativeExecutionV3_types___closed__5_once, _init_l_NativeExecutionV3_types___closed__5);
v___x_1288_ = lean_string_append(v___x_1287_, v___x_1286_);
return v___x_1288_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__10(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = ((lean_object*)(l_NativeExecutionV3_types___closed__9));
v___x_1291_ = lean_obj_once(&l_NativeExecutionV3_types___closed__8, &l_NativeExecutionV3_types___closed__8_once, _init_l_NativeExecutionV3_types___closed__8);
v___x_1292_ = lean_string_append(v___x_1291_, v___x_1290_);
return v___x_1292_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__11(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = ((lean_object*)(l_NativeExecutionV3_modelNames));
v___x_1294_ = ((lean_object*)(l_NativeExecutionV3_theoremNames));
v___x_1295_ = l_List_appendTR___redArg(v___x_1294_, v___x_1293_);
return v___x_1295_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__12(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = lean_obj_once(&l_NativeExecutionV3_types___closed__11, &l_NativeExecutionV3_types___closed__11_once, _init_l_NativeExecutionV3_types___closed__11);
v___x_1298_ = l_List_zipIdxTR___redArg(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__13(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = ((lean_object*)(l_NativeExecutionV3_modelNames));
v___x_1301_ = l_List_zipIdxTR___redArg(v___x_1300_, v___x_1299_);
return v___x_1301_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__15(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_obj_once(&l_NativeExecutionV3_types___closed__7, &l_NativeExecutionV3_types___closed__7_once, _init_l_NativeExecutionV3_types___closed__7);
v___x_1304_ = ((lean_object*)(l_NativeExecutionV3_types___closed__14));
v___x_1305_ = lean_string_append(v___x_1304_, v___x_1303_);
return v___x_1305_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__17(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1307_ = ((lean_object*)(l_NativeExecutionV3_types___closed__16));
v___x_1308_ = lean_obj_once(&l_NativeExecutionV3_types___closed__15, &l_NativeExecutionV3_types___closed__15_once, _init_l_NativeExecutionV3_types___closed__15);
v___x_1309_ = lean_string_append(v___x_1308_, v___x_1307_);
return v___x_1309_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__20(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_obj_once(&l_NativeExecutionV3_types___closed__6, &l_NativeExecutionV3_types___closed__6_once, _init_l_NativeExecutionV3_types___closed__6);
v___x_1313_ = lean_obj_once(&l_NativeExecutionV3_types___closed__1, &l_NativeExecutionV3_types___closed__1_once, _init_l_NativeExecutionV3_types___closed__1);
v___x_1314_ = lean_nat_add(v___x_1313_, v___x_1312_);
return v___x_1314_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__21(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_obj_once(&l_NativeExecutionV3_types___closed__20, &l_NativeExecutionV3_types___closed__20_once, _init_l_NativeExecutionV3_types___closed__20);
v___x_1316_ = l_Nat_reprFast(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__22(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_obj_once(&l_NativeExecutionV3_types___closed__21, &l_NativeExecutionV3_types___closed__21_once, _init_l_NativeExecutionV3_types___closed__21);
v___x_1318_ = ((lean_object*)(l_NativeExecutionV3_types___closed__19));
v___x_1319_ = lean_string_append(v___x_1318_, v___x_1317_);
return v___x_1319_;
}
}
static lean_object* _init_l_NativeExecutionV3_types___closed__24(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = ((lean_object*)(l_NativeExecutionV3_types___closed__23));
v___x_1322_ = lean_obj_once(&l_NativeExecutionV3_types___closed__22, &l_NativeExecutionV3_types___closed__22_once, _init_l_NativeExecutionV3_types___closed__22);
v___x_1323_ = lean_string_append(v___x_1322_, v___x_1321_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_types(lean_object* v_env_1324_, lean_object* v_out_1325_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((lean_object*)(l_NativeExecutionV3_theoremNames));
v___x_1328_ = lean_box(0);
lean_inc_ref(v_env_1324_);
v___x_1329_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg(v_env_1324_, v___x_1327_, v___x_1328_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref_known(v___x_1329_, 1);
v___x_1330_ = ((lean_object*)(l_NativeExecutionV3_modelNames));
lean_inc_ref(v_env_1324_);
v___x_1331_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg(v_env_1324_, v___x_1330_, v___x_1328_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec_ref_known(v___x_1331_, 1);
v___x_1332_ = lean_obj_once(&l_NativeExecutionV3_types___closed__10, &l_NativeExecutionV3_types___closed__10_once, _init_l_NativeExecutionV3_types___closed__10);
v___x_1333_ = l_NativeExecutionV3_emit(v___x_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec_ref_known(v___x_1333_, 1);
v___x_1334_ = lean_obj_once(&l_NativeExecutionV3_types___closed__11, &l_NativeExecutionV3_types___closed__11_once, _init_l_NativeExecutionV3_types___closed__11);
v___x_1335_ = lean_obj_once(&l_NativeExecutionV3_types___closed__12, &l_NativeExecutionV3_types___closed__12_once, _init_l_NativeExecutionV3_types___closed__12);
lean_inc_ref(v_out_1325_);
lean_inc_ref(v_env_1324_);
v___x_1336_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg(v_env_1324_, v_out_1325_, v___x_1335_, v___x_1328_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec_ref_known(v___x_1336_, 1);
v___x_1337_ = lean_obj_once(&l_NativeExecutionV3_types___closed__13, &l_NativeExecutionV3_types___closed__13_once, _init_l_NativeExecutionV3_types___closed__13);
lean_inc_ref(v_out_1325_);
lean_inc_ref(v_env_1324_);
v___x_1338_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg(v_env_1324_, v_out_1325_, v___x_1337_, v___x_1328_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_dec_ref_known(v___x_1338_, 1);
v___x_1339_ = lean_obj_once(&l_NativeExecutionV3_types___closed__17, &l_NativeExecutionV3_types___closed__17_once, _init_l_NativeExecutionV3_types___closed__17);
v___x_1340_ = l_NativeExecutionV3_emit(v___x_1339_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec_ref_known(v___x_1340_, 1);
v___x_1341_ = lean_box(0);
v___x_1342_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6___redArg(v_env_1324_, v___x_1334_, v___x_1341_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1344_ = ((lean_object*)(l_NativeExecutionV3_types___closed__18));
v___x_1345_ = lean_string_append(v_out_1325_, v___x_1344_);
v___x_1346_ = l_Lean_Json_mkObj(v_a_1343_);
lean_dec(v_a_1343_);
v___x_1347_ = l_NativeExecutionV3_jsonFile(v___x_1345_, v___x_1346_);
lean_dec_ref(v___x_1345_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec_ref_known(v___x_1347_, 1);
v___x_1348_ = lean_obj_once(&l_NativeExecutionV3_types___closed__24, &l_NativeExecutionV3_types___closed__24_once, _init_l_NativeExecutionV3_types___closed__24);
v___x_1349_ = l_NativeExecutionV3_emit(v___x_1348_);
return v___x_1349_;
}
else
{
return v___x_1347_;
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_out_1325_);
v_a_1350_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1342_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1342_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_dec_ref(v_out_1325_);
lean_dec_ref(v_env_1324_);
return v___x_1340_;
}
}
else
{
lean_dec_ref(v_out_1325_);
lean_dec_ref(v_env_1324_);
return v___x_1338_;
}
}
else
{
lean_dec_ref(v_out_1325_);
lean_dec_ref(v_env_1324_);
return v___x_1336_;
}
}
else
{
lean_dec_ref(v_out_1325_);
lean_dec_ref(v_env_1324_);
return v___x_1333_;
}
}
else
{
lean_dec_ref(v_out_1325_);
lean_dec_ref(v_env_1324_);
return v___x_1331_;
}
}
else
{
lean_dec_ref(v_out_1325_);
lean_dec_ref(v_env_1324_);
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_types___boxed(lean_object* v_env_1358_, lean_object* v_out_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_NativeExecutionV3_types(v_env_1358_, v_out_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0(lean_object* v_env_1362_, lean_object* v_as_1363_, lean_object* v_as_x27_1364_, lean_object* v_b_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___redArg(v_env_1362_, v_as_x27_1364_, v_b_1365_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0___boxed(lean_object* v_env_1369_, lean_object* v_as_1370_, lean_object* v_as_x27_1371_, lean_object* v_b_1372_, lean_object* v_a_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__0(v_env_1369_, v_as_1370_, v_as_x27_1371_, v_b_1372_, v_a_1373_);
lean_dec(v_as_x27_1371_);
lean_dec(v_as_1370_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1(lean_object* v_env_1376_, lean_object* v_as_1377_, lean_object* v_as_x27_1378_, lean_object* v_b_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___redArg(v_env_1376_, v_as_x27_1378_, v_b_1379_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1___boxed(lean_object* v_env_1383_, lean_object* v_as_1384_, lean_object* v_as_x27_1385_, lean_object* v_b_1386_, lean_object* v_a_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__1(v_env_1383_, v_as_1384_, v_as_x27_1385_, v_b_1386_, v_a_1387_);
lean_dec(v_as_x27_1385_);
lean_dec(v_as_1384_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2(lean_object* v_env_1390_, lean_object* v_as_1391_, lean_object* v_as_x27_1392_, lean_object* v_b_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___redArg(v_env_1390_, v_as_x27_1392_, v_b_1393_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2___boxed(lean_object* v_env_1397_, lean_object* v_as_1398_, lean_object* v_as_x27_1399_, lean_object* v_b_1400_, lean_object* v_a_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__2(v_env_1397_, v_as_1398_, v_as_x27_1399_, v_b_1400_, v_a_1401_);
lean_dec(v_as_x27_1399_);
lean_dec(v_as_1398_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3(lean_object* v_env_1404_, lean_object* v_out_1405_, lean_object* v_as_1406_, lean_object* v_as_x27_1407_, lean_object* v_b_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___redArg(v_env_1404_, v_out_1405_, v_as_x27_1407_, v_b_1408_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3___boxed(lean_object* v_env_1412_, lean_object* v_out_1413_, lean_object* v_as_1414_, lean_object* v_as_x27_1415_, lean_object* v_b_1416_, lean_object* v_a_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__3(v_env_1412_, v_out_1413_, v_as_1414_, v_as_x27_1415_, v_b_1416_, v_a_1417_);
lean_dec(v_as_x27_1415_);
lean_dec(v_as_1414_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4(lean_object* v_env_1420_, lean_object* v_out_1421_, lean_object* v_as_1422_, lean_object* v_as_x27_1423_, lean_object* v_b_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___redArg(v_env_1420_, v_out_1421_, v_as_x27_1423_, v_b_1424_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4___boxed(lean_object* v_env_1428_, lean_object* v_out_1429_, lean_object* v_as_1430_, lean_object* v_as_x27_1431_, lean_object* v_b_1432_, lean_object* v_a_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__4(v_env_1428_, v_out_1429_, v_as_1430_, v_as_x27_1431_, v_b_1432_, v_a_1433_);
lean_dec(v_as_x27_1431_);
lean_dec(v_as_1430_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6(lean_object* v_env_1436_, lean_object* v_as_1437_, lean_object* v_as_x27_1438_, lean_object* v_b_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6___redArg(v_env_1436_, v_as_x27_1438_, v_b_1439_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6___boxed(lean_object* v_env_1443_, lean_object* v_as_1444_, lean_object* v_as_x27_1445_, lean_object* v_b_1446_, lean_object* v_a_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_types_spec__6(v_env_1443_, v_as_1444_, v_as_x27_1445_, v_b_1446_, v_a_1447_);
lean_dec(v_as_x27_1445_);
lean_dec(v_as_1444_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg(lean_object* v_env_1452_, lean_object* v_a_1453_, lean_object* v_as_x27_1454_, lean_object* v_b_1455_){
_start:
{
if (lean_obj_tag(v_as_x27_1454_) == 0)
{
lean_object* v___x_1457_; 
lean_dec_ref(v_a_1453_);
lean_dec_ref(v_env_1452_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_b_1455_);
return v___x_1457_;
}
else
{
lean_object* v_head_1458_; lean_object* v_tail_1459_; lean_object* v___x_1460_; 
v_head_1458_ = lean_ctor_get(v_as_x27_1454_, 0);
v_tail_1459_ = lean_ctor_get(v_as_x27_1454_, 1);
lean_inc(v_head_1458_);
lean_inc_ref(v_env_1452_);
v___x_1460_ = l_NativeExecutionV3_info(v_env_1452_, v_head_1458_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1499_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1499_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1499_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; 
lean_inc(v_head_1458_);
lean_inc_ref(v_a_1453_);
v___x_1465_ = lean_environment_find(v_a_1453_, v_head_1458_);
if (lean_obj_tag(v___x_1465_) == 1)
{
lean_object* v_val_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1490_; 
v_val_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_val_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1490_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; uint8_t v___y_1472_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1470_ = lean_box(0);
v___x_1484_ = l_Lean_ConstantInfo_type(v_a_1461_);
v___x_1485_ = l_Lean_ConstantInfo_type(v_val_1466_);
v___x_1486_ = lean_expr_eqv(v___x_1484_, v___x_1485_);
lean_dec_ref(v___x_1485_);
lean_dec_ref(v___x_1484_);
if (v___x_1486_ == 0)
{
lean_dec(v_val_1466_);
lean_dec(v_a_1461_);
v___y_1472_ = v___x_1486_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1487_ = l_Lean_ConstantInfo_levelParams(v_a_1461_);
lean_dec(v_a_1461_);
v___x_1488_ = l_Lean_ConstantInfo_levelParams(v_val_1466_);
lean_dec(v_val_1466_);
v___x_1489_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v___x_1487_, v___x_1488_);
lean_dec(v___x_1488_);
lean_dec(v___x_1487_);
v___y_1472_ = v___x_1489_;
goto v___jp_1471_;
}
v___jp_1471_:
{
if (v___y_1472_ == 0)
{
lean_object* v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
lean_dec_ref(v_a_1453_);
lean_dec_ref(v_env_1452_);
v___x_1473_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___closed__0));
v___x_1474_ = 1;
lean_inc(v_head_1458_);
v___x_1475_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1458_, v___x_1474_);
v___x_1476_ = lean_string_append(v___x_1473_, v___x_1475_);
lean_dec_ref(v___x_1475_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set_tag(v___x_1468_, 18);
lean_ctor_set(v___x_1468_, 0, v___x_1476_);
v___x_1478_ = v___x_1468_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set_tag(v___x_1463_, 1);
lean_ctor_set(v___x_1463_, 0, v___x_1478_);
v___x_1480_ = v___x_1463_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_del_object(v___x_1468_);
lean_del_object(v___x_1463_);
v_as_x27_1454_ = v_tail_1459_;
v_b_1455_ = v___x_1470_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
lean_dec(v___x_1465_);
lean_dec(v_a_1461_);
lean_dec_ref(v_a_1453_);
lean_dec_ref(v_env_1452_);
v___x_1491_ = ((lean_object*)(l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___closed__1));
v___x_1492_ = 1;
lean_inc(v_head_1458_);
v___x_1493_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1458_, v___x_1492_);
v___x_1494_ = lean_string_append(v___x_1491_, v___x_1493_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set_tag(v___x_1463_, 1);
lean_ctor_set(v___x_1463_, 0, v___x_1495_);
v___x_1497_ = v___x_1463_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v_a_1453_);
lean_dec_ref(v_env_1452_);
v_a_1500_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1460_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1460_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg___boxed(lean_object* v_env_1508_, lean_object* v_a_1509_, lean_object* v_as_x27_1510_, lean_object* v_b_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg(v_env_1508_, v_a_1509_, v_as_x27_1510_, v_b_1511_);
lean_dec(v_as_x27_1510_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00NativeExecutionV3_positive_spec__1(lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
if (lean_obj_tag(v_a_1514_) == 0)
{
lean_object* v___x_1516_; 
v___x_1516_ = l_List_reverse___redArg(v_a_1515_);
return v___x_1516_;
}
else
{
lean_object* v_head_1517_; lean_object* v_tail_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1528_; 
v_head_1517_ = lean_ctor_get(v_a_1514_, 0);
v_tail_1518_ = lean_ctor_get(v_a_1514_, 1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_a_1514_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1520_ = v_a_1514_;
v_isShared_1521_ = v_isSharedCheck_1528_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_tail_1518_);
lean_inc(v_head_1517_);
lean_dec(v_a_1514_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1528_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1522_ = 1;
v___x_1523_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_1517_, v___x_1522_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v_a_1515_);
lean_ctor_set(v___x_1520_, 0, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_a_1515_);
v___x_1525_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
v_a_1514_ = v_tail_1518_;
v_a_1515_ = v___x_1525_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_NativeExecutionV3_positive___closed__3(void){
_start:
{
lean_object* v___x_1532_; lean_object* v_roots_1533_; lean_object* v___x_1534_; 
v___x_1532_ = lean_box(0);
v_roots_1533_ = lean_obj_once(&l_NativeExecutionV3_types___closed__11, &l_NativeExecutionV3_types___closed__11_once, _init_l_NativeExecutionV3_types___closed__11);
v___x_1534_ = l_List_mapTR_loop___at___00NativeExecutionV3_positive_spec__1(v_roots_1533_, v___x_1532_);
return v___x_1534_;
}
}
static lean_object* _init_l_NativeExecutionV3_positive___closed__8(void){
_start:
{
lean_object* v_roots_1539_; lean_object* v___x_1540_; 
v_roots_1539_ = lean_obj_once(&l_NativeExecutionV3_types___closed__11, &l_NativeExecutionV3_types___closed__11_once, _init_l_NativeExecutionV3_types___closed__11);
v___x_1540_ = l_List_lengthTR___redArg(v_roots_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l_NativeExecutionV3_positive___closed__9(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_obj_once(&l_NativeExecutionV3_positive___closed__8, &l_NativeExecutionV3_positive___closed__8_once, _init_l_NativeExecutionV3_positive___closed__8);
v___x_1542_ = l_Nat_reprFast(v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_positive(lean_object* v_env_1544_, lean_object* v_out_1545_){
_start:
{
lean_object* v_roots_1547_; lean_object* v___x_1548_; 
v_roots_1547_ = lean_obj_once(&l_NativeExecutionV3_types___closed__11, &l_NativeExecutionV3_types___closed__11_once, _init_l_NativeExecutionV3_types___closed__11);
lean_inc_ref(v_env_1544_);
v___x_1548_ = l_NativeExecutionV3_collected(v_env_1544_, v_roots_1547_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = l_NativeExecutionV3_checkSafety(v_a_1549_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_size_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref_known(v___x_1550_, 1);
v_size_1551_ = lean_ctor_get(v_a_1549_, 0);
v___x_1552_ = ((lean_object*)(l_NativeExecutionV3_positive___closed__0));
lean_inc(v_size_1551_);
v___x_1553_ = l_Nat_reprFast(v_size_1551_);
v___x_1554_ = lean_string_append(v___x_1552_, v___x_1553_);
v___x_1555_ = ((lean_object*)(l_NativeExecutionV3_positive___closed__1));
v___x_1556_ = lean_string_append(v___x_1554_, v___x_1555_);
v___x_1557_ = l_NativeExecutionV3_emit(v___x_1556_);
if (lean_obj_tag(v___x_1557_) == 0)
{
uint32_t v___x_1558_; lean_object* v___x_1559_; 
lean_dec_ref_known(v___x_1557_, 1);
v___x_1558_ = 0;
v___x_1559_ = l_Lean_mkEmptyEnvironment(v___x_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v___x_1561_ = lean_elab_environment_to_kernel_env(v_a_1560_);
v___x_1562_ = l_Lean_Kernel_Environment_replay(v_a_1549_, v___x_1561_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = lean_box(0);
v___x_1565_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg(v_env_1544_, v_a_1563_, v_roots_1547_, v___x_1564_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_dec_ref_known(v___x_1565_, 1);
v___x_1566_ = ((lean_object*)(l_NativeExecutionV3_positive___closed__2));
lean_inc_ref(v_out_1545_);
v___x_1567_ = lean_string_append(v_out_1545_, v___x_1566_);
v___x_1568_ = lean_obj_once(&l_NativeExecutionV3_positive___closed__3, &l_NativeExecutionV3_positive___closed__3_once, _init_l_NativeExecutionV3_positive___closed__3);
v___x_1569_ = l_NativeExecutionV3_writeLines(v___x_1567_, v___x_1568_);
lean_dec_ref(v___x_1567_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_dec_ref_known(v___x_1569_, 1);
v___x_1570_ = ((lean_object*)(l_NativeExecutionV3_positive___closed__4));
lean_inc_ref(v_out_1545_);
v___x_1571_ = lean_string_append(v_out_1545_, v___x_1570_);
v___x_1572_ = l_NativeExecutionV3_sortedNames(v_a_1549_);
v___x_1573_ = l_NativeExecutionV3_writeLines(v___x_1571_, v___x_1572_);
lean_dec_ref(v___x_1571_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
lean_dec_ref_known(v___x_1573_, 1);
v___x_1574_ = ((lean_object*)(l_NativeExecutionV3_positive___closed__5));
v___x_1575_ = lean_string_append(v_out_1545_, v___x_1574_);
v___x_1576_ = l_NativeExecutionV3_axiomNames(v_a_1549_);
lean_dec(v_a_1549_);
v___x_1577_ = l_NativeExecutionV3_writeLines(v___x_1575_, v___x_1576_);
lean_dec_ref(v___x_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec_ref_known(v___x_1577_, 1);
v___x_1578_ = ((lean_object*)(l_NativeExecutionV3_positive___closed__6));
v___x_1579_ = lean_string_append(v___x_1578_, v___x_1553_);
lean_dec_ref(v___x_1553_);
v___x_1580_ = ((lean_object*)(l_NativeExecutionV3_positive___closed__7));
v___x_1581_ = lean_string_append(v___x_1579_, v___x_1580_);
v___x_1582_ = lean_obj_once(&l_NativeExecutionV3_positive___closed__9, &l_NativeExecutionV3_positive___closed__9_once, _init_l_NativeExecutionV3_positive___closed__9);
v___x_1583_ = lean_string_append(v___x_1581_, v___x_1582_);
v___x_1584_ = ((lean_object*)(l_NativeExecutionV3_positive___closed__10));
v___x_1585_ = lean_string_append(v___x_1583_, v___x_1584_);
v___x_1586_ = l_NativeExecutionV3_emit(v___x_1585_);
return v___x_1586_;
}
else
{
lean_dec_ref(v___x_1553_);
return v___x_1577_;
}
}
else
{
lean_dec_ref(v___x_1553_);
lean_dec(v_a_1549_);
lean_dec_ref(v_out_1545_);
return v___x_1573_;
}
}
else
{
lean_dec_ref(v___x_1553_);
lean_dec(v_a_1549_);
lean_dec_ref(v_out_1545_);
return v___x_1569_;
}
}
else
{
lean_dec_ref(v___x_1553_);
lean_dec(v_a_1549_);
lean_dec_ref(v_out_1545_);
return v___x_1565_;
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v___x_1553_);
lean_dec(v_a_1549_);
lean_dec_ref(v_out_1545_);
lean_dec_ref(v_env_1544_);
v_a_1587_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1562_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1562_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v___x_1553_);
lean_dec(v_a_1549_);
lean_dec_ref(v_out_1545_);
lean_dec_ref(v_env_1544_);
v_a_1595_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1559_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1559_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_dec_ref(v___x_1553_);
lean_dec(v_a_1549_);
lean_dec_ref(v_out_1545_);
lean_dec_ref(v_env_1544_);
return v___x_1557_;
}
}
else
{
lean_dec(v_a_1549_);
lean_dec_ref(v_out_1545_);
lean_dec_ref(v_env_1544_);
return v___x_1550_;
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_out_1545_);
lean_dec_ref(v_env_1544_);
v_a_1603_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1548_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1548_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_positive___boxed(lean_object* v_env_1611_, lean_object* v_out_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_NativeExecutionV3_positive(v_env_1611_, v_out_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0(lean_object* v_env_1615_, lean_object* v_a_1616_, lean_object* v_as_1617_, lean_object* v_as_x27_1618_, lean_object* v_b_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___redArg(v_env_1615_, v_a_1616_, v_as_x27_1618_, v_b_1619_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0___boxed(lean_object* v_env_1623_, lean_object* v_a_1624_, lean_object* v_as_1625_, lean_object* v_as_x27_1626_, lean_object* v_b_1627_, lean_object* v_a_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_List_forIn_x27_loop___at___00NativeExecutionV3_positive_spec__0(v_env_1623_, v_a_1624_, v_as_1625_, v_as_x27_1626_, v_b_1627_, v_a_1628_);
lean_dec(v_as_x27_1626_);
lean_dec(v_as_1625_);
return v_res_1630_;
}
}
static lean_object* _init_l_NativeExecutionV3_control___closed__15(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = lean_box(0);
v___x_1649_ = ((lean_object*)(l_NativeExecutionV3_control___closed__14));
v___x_1650_ = l_Lean_Expr_const___override(v___x_1649_, v___x_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_control(lean_object* v_env_1674_, lean_object* v_index_1675_, lean_object* v_out_1676_){
_start:
{
lean_object* v___x_1678_; uint8_t v___x_1679_; 
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_nat_dec_eq(v_index_1675_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = ((lean_object*)(l_NativeExecutionV3_theoremNames));
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_sub(v_index_1675_, v___x_1681_);
v___x_1683_ = l_List_get_x3fInternal___redArg(v___x_1680_, v___x_1682_);
if (lean_obj_tag(v___x_1683_) == 1)
{
lean_object* v_val_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1868_; 
v_val_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1868_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_val_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1868_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___y_1689_; uint8_t v_a_1690_; lean_object* v___y_1716_; lean_object* v___y_1717_; uint8_t v___y_1718_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1735_; lean_object* v_a_1736_; lean_object* v___x_1752_; 
lean_inc(v_val_1684_);
lean_inc_ref(v_env_1674_);
v___x_1752_ = l_NativeExecutionV3_info(v_env_1674_, v_val_1684_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1859_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1859_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1859_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
if (lean_obj_tag(v_a_1753_) == 2)
{
lean_object* v_val_1757_; lean_object* v_toConstantVal_1758_; lean_object* v_all_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1853_; 
v_val_1757_ = lean_ctor_get(v_a_1753_, 0);
lean_inc_ref(v_val_1757_);
v_toConstantVal_1758_ = lean_ctor_get(v_val_1757_, 0);
v_all_1759_ = lean_ctor_get(v_val_1757_, 2);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_val_1757_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v_val_1757_, 1);
lean_dec(v_unused_1854_);
v___x_1761_ = v_val_1757_;
v_isShared_1762_ = v_isSharedCheck_1853_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_all_1759_);
lean_inc(v_toConstantVal_1758_);
lean_dec(v_val_1757_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1853_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1763_ = ((lean_object*)(l_NativeExecutionV3_control___closed__14));
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_obj_once(&l_NativeExecutionV3_control___closed__15, &l_NativeExecutionV3_control___closed__15_once, _init_l_NativeExecutionV3_control___closed__15);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v___x_1765_);
v___x_1767_ = v___x_1761_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_toConstantVal_1758_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_all_1759_);
v___x_1767_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; uint8_t v___y_1770_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1768_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
v___x_1846_ = l_Lean_ConstantInfo_type(v___x_1768_);
v___x_1847_ = l_Lean_ConstantInfo_type(v_a_1753_);
v___x_1848_ = lean_expr_eqv(v___x_1846_, v___x_1847_);
lean_dec_ref(v___x_1847_);
lean_dec_ref(v___x_1846_);
if (v___x_1848_ == 0)
{
lean_dec_ref_known(v_a_1753_, 1);
v___y_1770_ = v___x_1848_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1849_ = l_Lean_ConstantInfo_levelParams(v___x_1768_);
v___x_1850_ = l_Lean_ConstantInfo_levelParams(v_a_1753_);
lean_dec_ref_known(v_a_1753_, 1);
v___x_1851_ = l_List_beq___at___00__private_Lean_Replay_0__Lean_Kernel_Environment_Replay_replayConstant_spec__4(v___x_1849_, v___x_1850_);
lean_dec(v___x_1850_);
lean_dec(v___x_1849_);
v___y_1770_ = v___x_1851_;
goto v___jp_1769_;
}
v___jp_1769_:
{
if (v___y_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
lean_dec_ref_known(v___x_1768_, 1);
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
lean_dec_ref(v_env_1674_);
v___x_1771_ = ((lean_object*)(l_NativeExecutionV3_control___closed__17));
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 1);
lean_ctor_set(v___x_1755_, 0, v___x_1771_);
v___x_1773_ = v___x_1755_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1755_);
lean_inc_ref(v___x_1768_);
v___x_1775_ = l_Lean_ConstantInfo_getUsedConstantsAsSet(v___x_1768_);
v___x_1776_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00NativeExecutionV3_collect_spec__0(v___x_1764_, v___x_1775_);
lean_dec(v___x_1775_);
v___x_1777_ = l_NativeExecutionV3_collected(v_env_1674_, v___x_1776_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1837_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1837_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1837_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
uint8_t v___x_1782_; 
v___x_1782_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg(v_a_1778_, v_val_1684_);
if (v___x_1782_ == 0)
{
uint8_t v___x_1783_; 
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg(v_a_1778_, v___x_1763_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec(v_a_1778_);
lean_dec_ref_known(v___x_1768_, 1);
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
v___x_1784_ = ((lean_object*)(l_NativeExecutionV3_control___closed__19));
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 1);
lean_ctor_set(v___x_1780_, 0, v___x_1784_);
v___x_1786_ = v___x_1780_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
lean_object* v___x_1788_; 
lean_del_object(v___x_1780_);
v___x_1788_ = l_NativeExecutionV3_checkSafety(v_a_1778_);
if (lean_obj_tag(v___x_1788_) == 0)
{
uint32_t v___x_1789_; lean_object* v___x_1790_; 
lean_dec_ref_known(v___x_1788_, 1);
v___x_1789_ = 0;
v___x_1790_ = l_Lean_mkEmptyEnvironment(v___x_1789_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = lean_elab_environment_to_kernel_env(v_a_1791_);
v___x_1793_ = l_Lean_Kernel_Environment_replay(v_a_1778_, v___x_1792_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_size_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_dec_ref_known(v___x_1793_, 1);
v_size_1794_ = lean_ctor_get(v_a_1778_, 0);
v___x_1795_ = ((lean_object*)(l_NativeExecutionV3_control___closed__20));
lean_inc(v_size_1794_);
v___x_1796_ = l_Nat_reprFast(v_size_1794_);
v___x_1797_ = lean_string_append(v___x_1795_, v___x_1796_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = ((lean_object*)(l_NativeExecutionV3_control___closed__21));
v___x_1799_ = lean_string_append(v___x_1797_, v___x_1798_);
v___x_1800_ = l_NativeExecutionV3_emit(v___x_1799_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref_known(v___x_1800_, 1);
v___x_1801_ = l_Lean_mkEmptyEnvironment(v___x_1789_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
lean_inc(v_val_1684_);
lean_inc(v_a_1778_);
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_a_1778_, v_val_1684_, v___x_1768_);
v___x_1804_ = lean_elab_environment_to_kernel_env(v_a_1802_);
v___x_1805_ = l_Lean_Kernel_Environment_replay(v___x_1803_, v___x_1804_);
lean_dec_ref(v___x_1803_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1813_; 
lean_del_object(v___x_1686_);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v___x_1805_, 0);
lean_dec(v_unused_1814_);
v___x_1807_ = v___x_1805_;
v_isShared_1808_ = v_isSharedCheck_1813_;
goto v_resetjp_1806_;
}
else
{
lean_dec(v___x_1805_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1813_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
if (v___x_1782_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
lean_dec(v_a_1778_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
v___x_1809_ = ((lean_object*)(l_NativeExecutionV3_control___closed__23));
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 1);
lean_ctor_set(v___x_1807_, 0, v___x_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
else
{
lean_del_object(v___x_1807_);
v___y_1689_ = v_a_1778_;
v_a_1690_ = v___x_1782_;
goto v___jp_1688_;
}
}
}
else
{
lean_object* v_a_1815_; 
v_a_1815_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1805_, 1);
v___y_1735_ = v_a_1778_;
v_a_1736_ = v_a_1815_;
goto v___jp_1734_;
}
}
else
{
lean_object* v_a_1816_; 
lean_dec_ref_known(v___x_1768_, 1);
v_a_1816_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1801_, 1);
v___y_1735_ = v_a_1778_;
v_a_1736_ = v_a_1816_;
goto v___jp_1734_;
}
}
else
{
lean_dec(v_a_1778_);
lean_dec_ref_known(v___x_1768_, 1);
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
return v___x_1800_;
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_a_1778_);
lean_dec_ref_known(v___x_1768_, 1);
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
v_a_1817_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1793_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1793_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_a_1778_);
lean_dec_ref_known(v___x_1768_, 1);
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
v_a_1825_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1790_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1790_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
else
{
lean_dec(v_a_1778_);
lean_dec_ref_known(v___x_1768_, 1);
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
return v___x_1788_;
}
}
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_dec(v_a_1778_);
lean_dec_ref_known(v___x_1768_, 1);
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
v___x_1833_ = ((lean_object*)(l_NativeExecutionV3_control___closed__25));
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 1);
lean_ctor_set(v___x_1780_, 0, v___x_1833_);
v___x_1835_ = v___x_1780_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref_known(v___x_1768_, 1);
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
v_a_1838_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1777_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1777_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec(v_a_1753_);
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
lean_dec_ref(v_env_1674_);
v___x_1855_ = ((lean_object*)(l_NativeExecutionV3_control___closed__27));
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 1);
lean_ctor_set(v___x_1755_, 0, v___x_1855_);
v___x_1857_ = v___x_1755_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1686_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
lean_dec_ref(v_env_1674_);
v_a_1860_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1752_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1752_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
v___jp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1691_ = ((lean_object*)(l_NativeExecutionV3_control___closed__0));
v___x_1692_ = lean_string_append(v_out_1676_, v___x_1691_);
v___x_1693_ = l_Nat_reprFast(v_index_1675_);
v___x_1694_ = lean_string_append(v___x_1692_, v___x_1693_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = ((lean_object*)(l_NativeExecutionV3_control___closed__1));
lean_inc_ref(v___x_1694_);
v___x_1696_ = lean_string_append(v___x_1694_, v___x_1695_);
v___x_1697_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1684_, v_a_1690_);
v___x_1698_ = lean_box(0);
lean_inc_ref(v___x_1697_);
v___x_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_NativeExecutionV3_writeLines(v___x_1696_, v___x_1699_);
lean_dec_ref(v___x_1696_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec_ref_known(v___x_1700_, 1);
v___x_1701_ = ((lean_object*)(l_NativeExecutionV3_control___closed__2));
lean_inc_ref(v___x_1694_);
v___x_1702_ = lean_string_append(v___x_1694_, v___x_1701_);
v___x_1703_ = l_NativeExecutionV3_sortedNames(v___y_1689_);
v___x_1704_ = l_NativeExecutionV3_writeLines(v___x_1702_, v___x_1703_);
lean_dec_ref(v___x_1702_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec_ref_known(v___x_1704_, 1);
v___x_1705_ = ((lean_object*)(l_NativeExecutionV3_control___closed__3));
v___x_1706_ = lean_string_append(v___x_1694_, v___x_1705_);
v___x_1707_ = l_NativeExecutionV3_axiomNames(v___y_1689_);
lean_dec_ref(v___y_1689_);
v___x_1708_ = l_NativeExecutionV3_writeLines(v___x_1706_, v___x_1707_);
lean_dec_ref(v___x_1706_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
lean_dec_ref_known(v___x_1708_, 1);
v___x_1709_ = ((lean_object*)(l_NativeExecutionV3_control___closed__4));
v___x_1710_ = lean_string_append(v___x_1709_, v___x_1697_);
v___x_1711_ = l_NativeExecutionV3_emit(v___x_1710_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref_known(v___x_1711_, 1);
v___x_1712_ = ((lean_object*)(l_NativeExecutionV3_control___closed__5));
v___x_1713_ = lean_string_append(v___x_1712_, v___x_1697_);
lean_dec_ref(v___x_1697_);
v___x_1714_ = l_NativeExecutionV3_emit(v___x_1713_);
return v___x_1714_;
}
else
{
lean_dec_ref(v___x_1697_);
return v___x_1711_;
}
}
else
{
lean_dec_ref(v___x_1697_);
return v___x_1708_;
}
}
else
{
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___y_1689_);
return v___x_1704_;
}
}
else
{
lean_dec_ref(v___x_1697_);
lean_dec_ref(v___x_1694_);
lean_dec_ref(v___y_1689_);
return v___x_1700_;
}
}
v___jp_1715_:
{
if (v___y_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
lean_dec_ref(v___y_1717_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
v___x_1719_ = ((lean_object*)(l_NativeExecutionV3_control___closed__6));
v___x_1720_ = lean_string_append(v___x_1719_, v___y_1716_);
lean_dec_ref(v___y_1716_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 18);
lean_ctor_set(v___x_1686_, 0, v___x_1720_);
v___x_1722_ = v___x_1686_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_del_object(v___x_1686_);
v___x_1725_ = ((lean_object*)(l_NativeExecutionV3_control___closed__7));
v___x_1726_ = lean_string_append(v___x_1725_, v___y_1716_);
lean_dec_ref(v___y_1716_);
v___x_1727_ = l_NativeExecutionV3_emit(v___x_1726_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_dec_ref_known(v___x_1727_, 1);
v___y_1689_ = v___y_1717_;
v_a_1690_ = v___y_1718_;
goto v___jp_1688_;
}
else
{
lean_dec_ref(v___y_1717_);
lean_dec(v_val_1684_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
return v___x_1727_;
}
}
}
v___jp_1728_:
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = l_List_lengthTR___redArg(v___y_1731_);
lean_dec(v___y_1731_);
v___x_1733_ = lean_nat_dec_lt(v___x_1681_, v___x_1732_);
lean_dec(v___x_1732_);
v___y_1716_ = v___y_1729_;
v___y_1717_ = v___y_1730_;
v___y_1718_ = v___x_1733_;
goto v___jp_1715_;
}
v___jp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1737_ = lean_io_error_to_string(v_a_1736_);
v___x_1738_ = ((lean_object*)(l_NativeExecutionV3_control___closed__8));
v___x_1739_ = lean_box(0);
v___x_1740_ = l_String_splitOnAux(v___x_1737_, v___x_1738_, v___x_1678_, v___x_1678_, v___x_1678_, v___x_1739_);
v___x_1741_ = l_List_lengthTR___redArg(v___x_1740_);
lean_dec(v___x_1740_);
v___x_1742_ = lean_nat_dec_lt(v___x_1681_, v___x_1741_);
lean_dec(v___x_1741_);
if (v___x_1742_ == 0)
{
v___y_1716_ = v___x_1737_;
v___y_1717_ = v___y_1735_;
v___y_1718_ = v___x_1742_;
goto v___jp_1715_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1743_ = ((lean_object*)(l_NativeExecutionV3_control___closed__9));
lean_inc(v_val_1684_);
v___x_1744_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_1684_, v___x_1742_);
v___x_1745_ = lean_string_append(v___x_1743_, v___x_1744_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = ((lean_object*)(l_NativeExecutionV3_control___closed__10));
v___x_1747_ = lean_string_append(v___x_1745_, v___x_1746_);
v___x_1748_ = ((lean_object*)(l_NativeExecutionV3_control___closed__11));
v___x_1749_ = lean_string_dec_eq(v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
v___x_1750_ = l_String_splitOnAux(v___x_1737_, v___x_1747_, v___x_1678_, v___x_1678_, v___x_1678_, v___x_1739_);
lean_dec_ref(v___x_1747_);
v___y_1729_ = v___x_1737_;
v___y_1730_ = v___y_1735_;
v___y_1731_ = v___x_1750_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1751_; 
lean_dec_ref(v___x_1747_);
lean_inc_ref(v___x_1737_);
v___x_1751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1737_);
lean_ctor_set(v___x_1751_, 1, v___x_1739_);
v___y_1729_ = v___x_1737_;
v___y_1730_ = v___y_1735_;
v___y_1731_ = v___x_1751_;
goto v___jp_1728_;
}
}
}
}
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
lean_dec(v___x_1683_);
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
lean_dec_ref(v_env_1674_);
v___x_1869_ = ((lean_object*)(l_NativeExecutionV3_control___closed__29));
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
lean_dec_ref(v_out_1676_);
lean_dec(v_index_1675_);
lean_dec_ref(v_env_1674_);
v___x_1871_ = ((lean_object*)(l_NativeExecutionV3_control___closed__31));
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_NativeExecutionV3_control___boxed(lean_object* v_env_1873_, lean_object* v_index_1874_, lean_object* v_out_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_NativeExecutionV3_control(v_env_1873_, v_index_1874_, v_out_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_1904_){
_start:
{
size_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1906_ = ((size_t)4194304000ULL);
v___x_1907_ = lean_internal_set_max_memory(v___x_1906_);
v___x_1908_ = ((lean_object*)(l_main___closed__0));
v___x_1909_ = l_NativeExecutionV3_emit(v___x_1908_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_dec_ref_known(v___x_1909_, 1);
v___x_1910_ = ((lean_object*)(l_main___closed__1));
v___x_1911_ = l_Lean_findSysroot(v___x_1910_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = lean_box(0);
v___x_1914_ = l_Lean_initSearchPath(v_a_1912_, v___x_1913_);
if (lean_obj_tag(v___x_1914_) == 0)
{
uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint32_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_dec_ref_known(v___x_1914_, 1);
v___x_1915_ = 0;
v___x_1916_ = ((lean_object*)(l_main___closed__5));
v___x_1917_ = l_Lean_Options_empty;
v___x_1918_ = 0;
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = ((lean_object*)(l_main___closed__6));
v___x_1921_ = 2;
v___x_1922_ = lean_box(1);
v___x_1923_ = l_Lean_importModules(v___x_1916_, v___x_1917_, v___x_1918_, v___x_1920_, v___x_1915_, v___x_1915_, v___x_1921_, v___x_1922_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1968_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1926_ = v___x_1923_;
v_isShared_1927_ = v_isSharedCheck_1968_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1923_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1968_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l_main___closed__7));
v___x_1929_ = l_NativeExecutionV3_emit(v___x_1928_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1966_; 
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v___x_1929_, 0);
lean_dec(v_unused_1967_);
v___x_1931_ = v___x_1929_;
v_isShared_1932_ = v_isSharedCheck_1966_;
goto v_resetjp_1930_;
}
else
{
lean_dec(v___x_1929_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1966_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
if (lean_obj_tag(v_args_1904_) == 1)
{
lean_object* v_head_1938_; lean_object* v_tail_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v_head_1938_ = lean_ctor_get(v_args_1904_, 0);
lean_inc(v_head_1938_);
v_tail_1939_ = lean_ctor_get(v_args_1904_, 1);
lean_inc(v_tail_1939_);
lean_dec_ref_known(v_args_1904_, 2);
v___x_1940_ = l_Lean_Environment_setExporting(v_a_1924_, v___x_1915_);
v___x_1941_ = ((lean_object*)(l_main___closed__10));
v___x_1942_ = lean_string_dec_eq(v_head_1938_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1943_ = ((lean_object*)(l_main___closed__11));
v___x_1944_ = lean_string_dec_eq(v_head_1938_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_main___closed__12));
v___x_1946_ = lean_string_dec_eq(v_head_1938_, v___x_1945_);
lean_dec(v_head_1938_);
if (v___x_1946_ == 0)
{
lean_dec_ref(v___x_1940_);
lean_dec(v_tail_1939_);
lean_del_object(v___x_1926_);
goto v___jp_1933_;
}
else
{
if (lean_obj_tag(v_tail_1939_) == 1)
{
lean_object* v_tail_1947_; 
v_tail_1947_ = lean_ctor_get(v_tail_1939_, 1);
lean_inc(v_tail_1947_);
if (lean_obj_tag(v_tail_1947_) == 1)
{
lean_object* v_tail_1948_; 
v_tail_1948_ = lean_ctor_get(v_tail_1947_, 1);
if (lean_obj_tag(v_tail_1948_) == 0)
{
lean_object* v_head_1949_; lean_object* v_head_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_del_object(v___x_1931_);
v_head_1949_ = lean_ctor_get(v_tail_1939_, 0);
lean_inc(v_head_1949_);
lean_dec_ref_known(v_tail_1939_, 2);
v_head_1950_ = lean_ctor_get(v_tail_1947_, 0);
lean_inc(v_head_1950_);
lean_dec_ref_known(v_tail_1947_, 2);
v___x_1951_ = lean_string_utf8_byte_size(v_head_1949_);
v___x_1952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1952_, 0, v_head_1949_);
lean_ctor_set(v___x_1952_, 1, v___x_1919_);
lean_ctor_set(v___x_1952_, 2, v___x_1951_);
v___x_1953_ = l_String_Slice_toNat_x3f(v___x_1952_);
lean_dec_ref_known(v___x_1952_, 3);
if (lean_obj_tag(v___x_1953_) == 1)
{
lean_object* v_val_1954_; lean_object* v___x_1955_; 
lean_del_object(v___x_1926_);
v_val_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_val_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = l_NativeExecutionV3_control(v___x_1940_, v_val_1954_, v_head_1950_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
lean_dec(v___x_1953_);
lean_dec(v_head_1950_);
lean_dec_ref(v___x_1940_);
v___x_1956_ = ((lean_object*)(l_main___closed__14));
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 1);
lean_ctor_set(v___x_1926_, 0, v___x_1956_);
v___x_1958_ = v___x_1926_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
else
{
lean_dec_ref_known(v_tail_1947_, 2);
lean_dec_ref_known(v_tail_1939_, 2);
lean_dec_ref(v___x_1940_);
lean_del_object(v___x_1926_);
goto v___jp_1933_;
}
}
else
{
lean_dec(v_tail_1947_);
lean_dec_ref_known(v_tail_1939_, 2);
lean_dec_ref(v___x_1940_);
lean_del_object(v___x_1926_);
goto v___jp_1933_;
}
}
else
{
lean_dec_ref(v___x_1940_);
lean_dec(v_tail_1939_);
lean_del_object(v___x_1926_);
goto v___jp_1933_;
}
}
}
else
{
lean_dec(v_head_1938_);
lean_del_object(v___x_1926_);
if (lean_obj_tag(v_tail_1939_) == 1)
{
lean_object* v_tail_1960_; 
v_tail_1960_ = lean_ctor_get(v_tail_1939_, 1);
if (lean_obj_tag(v_tail_1960_) == 0)
{
lean_object* v_head_1961_; lean_object* v___x_1962_; 
lean_del_object(v___x_1931_);
v_head_1961_ = lean_ctor_get(v_tail_1939_, 0);
lean_inc(v_head_1961_);
lean_dec_ref_known(v_tail_1939_, 2);
v___x_1962_ = l_NativeExecutionV3_positive(v___x_1940_, v_head_1961_);
return v___x_1962_;
}
else
{
lean_dec_ref_known(v_tail_1939_, 2);
lean_dec_ref(v___x_1940_);
goto v___jp_1933_;
}
}
else
{
lean_dec_ref(v___x_1940_);
lean_dec(v_tail_1939_);
goto v___jp_1933_;
}
}
}
else
{
lean_dec(v_head_1938_);
lean_del_object(v___x_1926_);
if (lean_obj_tag(v_tail_1939_) == 1)
{
lean_object* v_tail_1963_; 
v_tail_1963_ = lean_ctor_get(v_tail_1939_, 1);
if (lean_obj_tag(v_tail_1963_) == 0)
{
lean_object* v_head_1964_; lean_object* v___x_1965_; 
lean_del_object(v___x_1931_);
v_head_1964_ = lean_ctor_get(v_tail_1939_, 0);
lean_inc(v_head_1964_);
lean_dec_ref_known(v_tail_1939_, 2);
v___x_1965_ = l_NativeExecutionV3_types(v___x_1940_, v_head_1964_);
return v___x_1965_;
}
else
{
lean_dec_ref_known(v_tail_1939_, 2);
lean_dec_ref(v___x_1940_);
goto v___jp_1933_;
}
}
else
{
lean_dec_ref(v___x_1940_);
lean_dec(v_tail_1939_);
goto v___jp_1933_;
}
}
}
else
{
lean_del_object(v___x_1926_);
lean_dec(v_a_1924_);
lean_dec(v_args_1904_);
goto v___jp_1933_;
}
v___jp_1933_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = ((lean_object*)(l_main___closed__9));
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 1);
lean_ctor_set(v___x_1931_, 0, v___x_1934_);
v___x_1936_ = v___x_1931_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_del_object(v___x_1926_);
lean_dec(v_a_1924_);
lean_dec(v_args_1904_);
return v___x_1929_;
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v_args_1904_);
v_a_1969_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1923_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1923_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_dec(v_args_1904_);
return v___x_1914_;
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v_args_1904_);
v_a_1977_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1911_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1911_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
else
{
lean_dec(v_args_1904_);
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_1985_, lean_object* v_a_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = _lean_main(v_args_1985_);
return v_res_1987_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_Replay(uint8_t builtin);
lean_object* initialize_Lean_Util_Path(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Driver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Replay(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    lean_object* in = lean_box(0);
    int i = argc;
    while (i > 1) {
      lean_object* n;
      i--;
      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
      in = n;
    }
    return _lean_main(in);
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  res = initialize_Driver(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = 0;
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
