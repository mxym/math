// Lean compiler output
// Module: Diagnostic
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object*);
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* lean_internal_set_max_memory(size_t);
LEAN_EXPORT lean_object* l_setDiagnosticMaxMemory___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Missing/wrong theorem "};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__0___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "DATA_ONLY_THEOREM_PRESENT "};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Missing/wrong definition "};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "DATA_ONLY_DEFINITION_PRESENT "};
static const lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "DIAGNOSTIC_MAX_MEMORY_BYTES 4194304000"};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_string_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "NativeExecutionAudit"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_ctor_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__2_value),LEAN_SCALAR_PTR_LITERAL(123, 166, 59, 239, 82, 229, 80, 226)}};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static const lean_ctor_object l_main___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_main___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_main___closed__4 = (const lean_object*)&l_main___closed__4_value;
static const lean_array_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_main___closed__4_value)}};
static const lean_object* l_main___closed__5 = (const lean_object*)&l_main___closed__5_value;
static const lean_array_object l_main___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__6 = (const lean_object*)&l_main___closed__6_value;
static const lean_string_object l_main___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ConcreteNativeExtraction"};
static const lean_object* l_main___closed__7 = (const lean_object*)&l_main___closed__7_value;
static const lean_string_object l_main___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "concrete_assembled_compiler_exists"};
static const lean_object* l_main___closed__8 = (const lean_object*)&l_main___closed__8_value;
static const lean_ctor_object l_main___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__7_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_main___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__9_value_aux_0),((lean_object*)&l_main___closed__8_value),LEAN_SCALAR_PTR_LITERAL(245, 195, 91, 172, 81, 196, 241, 124)}};
static const lean_object* l_main___closed__9 = (const lean_object*)&l_main___closed__9_value;
static const lean_string_object l_main___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "assembledRun_accounted_actions"};
static const lean_object* l_main___closed__10 = (const lean_object*)&l_main___closed__10_value;
static const lean_ctor_object l_main___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__7_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_main___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__11_value_aux_0),((lean_object*)&l_main___closed__10_value),LEAN_SCALAR_PTR_LITERAL(186, 15, 253, 119, 231, 197, 3, 90)}};
static const lean_object* l_main___closed__11 = (const lean_object*)&l_main___closed__11_value;
static const lean_string_object l_main___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "assembledRun_erase"};
static const lean_object* l_main___closed__12 = (const lean_object*)&l_main___closed__12_value;
static const lean_ctor_object l_main___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__7_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_main___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__13_value_aux_0),((lean_object*)&l_main___closed__12_value),LEAN_SCALAR_PTR_LITERAL(183, 206, 153, 34, 247, 38, 250, 159)}};
static const lean_object* l_main___closed__13 = (const lean_object*)&l_main___closed__13_value;
static const lean_ctor_object l_main___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___closed__14 = (const lean_object*)&l_main___closed__14_value;
static const lean_ctor_object l_main___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__11_value),((lean_object*)&l_main___closed__14_value)}};
static const lean_object* l_main___closed__15 = (const lean_object*)&l_main___closed__15_value;
static const lean_ctor_object l_main___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__9_value),((lean_object*)&l_main___closed__15_value)}};
static const lean_object* l_main___closed__16 = (const lean_object*)&l_main___closed__16_value;
static const lean_string_object l_main___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "assembledRun"};
static const lean_object* l_main___closed__17 = (const lean_object*)&l_main___closed__17_value;
static const lean_ctor_object l_main___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__7_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_main___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__18_value_aux_0),((lean_object*)&l_main___closed__17_value),LEAN_SCALAR_PTR_LITERAL(39, 155, 147, 103, 167, 87, 87, 121)}};
static const lean_object* l_main___closed__18 = (const lean_object*)&l_main___closed__18_value;
static const lean_string_object l_main___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "assembledPrimitiveBound"};
static const lean_object* l_main___closed__19 = (const lean_object*)&l_main___closed__19_value;
static const lean_ctor_object l_main___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_main___closed__7_value),LEAN_SCALAR_PTR_LITERAL(240, 38, 148, 59, 127, 184, 133, 65)}};
static const lean_ctor_object l_main___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__20_value_aux_0),((lean_object*)&l_main___closed__19_value),LEAN_SCALAR_PTR_LITERAL(169, 22, 234, 167, 83, 25, 187, 42)}};
static const lean_object* l_main___closed__20 = (const lean_object*)&l_main___closed__20_value;
static const lean_ctor_object l_main___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___closed__21 = (const lean_object*)&l_main___closed__21_value;
static const lean_ctor_object l_main___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_main___closed__18_value),((lean_object*)&l_main___closed__21_value)}};
static const lean_object* l_main___closed__22 = (const lean_object*)&l_main___closed__22_value;
static const lean_string_object l_main___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "DATA_ONLY_IMPORT_DIAGNOSTIC_COMPLETE_NOT_KERNEL_REPLAY"};
static const lean_object* l_main___closed__23 = (const lean_object*)&l_main___closed__23_value;
LEAN_EXPORT lean_object* _lean_main();
LEAN_EXPORT lean_object* l_main___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_setDiagnosticMaxMemory___boxed(lean_object* v_max_3_, lean_object* v_a_00___x40___internal___hyg_4_){
_start:
{
size_t v_max_boxed_5_; lean_object* v_res_6_; 
v_max_boxed_5_ = lean_unbox_usize(v_max_3_);
lean_dec(v_max_3_);
v_res_6_ = lean_internal_set_max_memory(v_max_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__0___redArg(lean_object* v_a_9_, lean_object* v_as_x27_10_, lean_object* v_b_11_){
_start:
{
if (lean_obj_tag(v_as_x27_10_) == 0)
{
lean_object* v___x_13_; 
lean_dec_ref(v_a_9_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v_b_11_);
return v___x_13_;
}
else
{
lean_object* v_head_14_; lean_object* v_tail_15_; uint8_t v___x_23_; lean_object* v___x_24_; 
v_head_14_ = lean_ctor_get(v_as_x27_10_, 0);
v_tail_15_ = lean_ctor_get(v_as_x27_10_, 1);
v___x_23_ = 0;
lean_inc(v_head_14_);
lean_inc_ref(v_a_9_);
v___x_24_ = l_Lean_Environment_find_x3f(v_a_9_, v_head_14_, v___x_23_);
if (lean_obj_tag(v___x_24_) == 1)
{
lean_object* v_val_25_; 
v_val_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_val_25_);
lean_dec_ref_known(v___x_24_, 1);
if (lean_obj_tag(v_val_25_) == 2)
{
lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec_ref_known(v_val_25_, 1);
v___x_26_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__0___redArg___closed__1));
v___x_27_ = 1;
lean_inc(v_head_14_);
v___x_28_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_14_, v___x_27_);
v___x_29_ = lean_string_append(v___x_26_, v___x_28_);
lean_dec_ref(v___x_28_);
v___x_30_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_29_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v___x_31_; 
lean_dec_ref_known(v___x_30_, 1);
v___x_31_ = lean_box(0);
v_as_x27_10_ = v_tail_15_;
v_b_11_ = v___x_31_;
goto _start;
}
else
{
lean_dec_ref(v_a_9_);
return v___x_30_;
}
}
else
{
lean_dec(v_val_25_);
lean_dec_ref(v_a_9_);
goto v___jp_16_;
}
}
else
{
lean_dec(v___x_24_);
lean_dec_ref(v_a_9_);
goto v___jp_16_;
}
v___jp_16_:
{
lean_object* v___x_17_; uint8_t v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_17_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__0___redArg___closed__0));
v___x_18_ = 1;
lean_inc(v_head_14_);
v___x_19_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_14_, v___x_18_);
v___x_20_ = lean_string_append(v___x_17_, v___x_19_);
lean_dec_ref(v___x_19_);
v___x_21_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__0___redArg___boxed(lean_object* v_a_33_, lean_object* v_as_x27_34_, lean_object* v_b_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_List_forIn_x27_loop___at___00main_spec__0___redArg(v_a_33_, v_as_x27_34_, v_b_35_);
lean_dec(v_as_x27_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg(lean_object* v_a_40_, lean_object* v_as_x27_41_, lean_object* v_b_42_){
_start:
{
if (lean_obj_tag(v_as_x27_41_) == 0)
{
lean_object* v___x_44_; 
lean_dec_ref(v_a_40_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v_b_42_);
return v___x_44_;
}
else
{
lean_object* v_head_45_; lean_object* v_tail_46_; uint8_t v___x_54_; lean_object* v___x_55_; 
v_head_45_ = lean_ctor_get(v_as_x27_41_, 0);
v_tail_46_ = lean_ctor_get(v_as_x27_41_, 1);
v___x_54_ = 0;
lean_inc(v_head_45_);
lean_inc_ref(v_a_40_);
v___x_55_ = l_Lean_Environment_find_x3f(v_a_40_, v_head_45_, v___x_54_);
if (lean_obj_tag(v___x_55_) == 1)
{
lean_object* v_val_56_; 
v_val_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_val_56_);
lean_dec_ref_known(v___x_55_, 1);
if (lean_obj_tag(v_val_56_) == 1)
{
lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
lean_dec_ref_known(v_val_56_, 1);
v___x_57_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__1));
v___x_58_ = 1;
lean_inc(v_head_45_);
v___x_59_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_45_, v___x_58_);
v___x_60_ = lean_string_append(v___x_57_, v___x_59_);
lean_dec_ref(v___x_59_);
v___x_61_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_60_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v___x_62_; 
lean_dec_ref_known(v___x_61_, 1);
v___x_62_ = lean_box(0);
v_as_x27_41_ = v_tail_46_;
v_b_42_ = v___x_62_;
goto _start;
}
else
{
lean_dec_ref(v_a_40_);
return v___x_61_;
}
}
else
{
lean_dec(v_val_56_);
lean_dec_ref(v_a_40_);
goto v___jp_47_;
}
}
else
{
lean_dec(v___x_55_);
lean_dec_ref(v_a_40_);
goto v___jp_47_;
}
v___jp_47_:
{
lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_48_ = ((lean_object*)(l_List_forIn_x27_loop___at___00main_spec__1___redArg___closed__0));
v___x_49_ = 1;
lean_inc(v_head_45_);
v___x_50_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_45_, v___x_49_);
v___x_51_ = lean_string_append(v___x_48_, v___x_50_);
lean_dec_ref(v___x_50_);
v___x_52_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___redArg___boxed(lean_object* v_a_64_, lean_object* v_as_x27_65_, lean_object* v_b_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_a_64_, v_as_x27_65_, v_b_66_);
lean_dec(v_as_x27_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* _lean_main(){
_start:
{
size_t v_cap_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_cap_122_ = ((size_t)4194304000ULL);
v___x_123_ = lean_internal_set_max_memory(v_cap_122_);
v___x_124_ = ((lean_object*)(l_main___closed__0));
v___x_125_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_124_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec_ref_known(v___x_125_, 1);
v___x_126_ = ((lean_object*)(l_main___closed__1));
v___x_127_ = l_Lean_findSysroot(v___x_126_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_127_, 1);
v___x_129_ = lean_box(0);
v___x_130_ = l_Lean_initSearchPath(v_a_128_, v___x_129_);
if (lean_obj_tag(v___x_130_) == 0)
{
uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint32_t v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec_ref_known(v___x_130_, 1);
v___x_131_ = 0;
v___x_132_ = ((lean_object*)(l_main___closed__5));
v___x_133_ = l_Lean_Options_empty;
v___x_134_ = 0;
v___x_135_ = ((lean_object*)(l_main___closed__6));
v___x_136_ = 2;
v___x_137_ = lean_box(1);
v___x_138_ = l_Lean_importModules(v___x_132_, v___x_133_, v___x_134_, v___x_135_, v___x_131_, v___x_131_, v___x_136_, v___x_137_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc_n(v_a_139_, 2);
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = ((lean_object*)(l_main___closed__16));
v___x_141_ = lean_box(0);
v___x_142_ = l_List_forIn_x27_loop___at___00main_spec__0___redArg(v_a_139_, v___x_140_, v___x_141_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec_ref_known(v___x_142_, 1);
v___x_143_ = ((lean_object*)(l_main___closed__22));
v___x_144_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_a_139_, v___x_143_, v___x_141_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec_ref_known(v___x_144_, 1);
v___x_145_ = ((lean_object*)(l_main___closed__23));
v___x_146_ = l_IO_println___at___00__private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(v___x_145_);
return v___x_146_;
}
else
{
return v___x_144_;
}
}
else
{
lean_dec(v_a_139_);
return v___x_142_;
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_138_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_138_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
else
{
return v___x_130_;
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_a_155_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_127_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_127_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
else
{
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = _lean_main();
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__0(lean_object* v_a_165_, lean_object* v_as_166_, lean_object* v_as_x27_167_, lean_object* v_b_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_List_forIn_x27_loop___at___00main_spec__0___redArg(v_a_165_, v_as_x27_167_, v_b_168_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__0___boxed(lean_object* v_a_172_, lean_object* v_as_173_, lean_object* v_as_x27_174_, lean_object* v_b_175_, lean_object* v_a_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_List_forIn_x27_loop___at___00main_spec__0(v_a_172_, v_as_173_, v_as_x27_174_, v_b_175_, v_a_176_);
lean_dec(v_as_x27_174_);
lean_dec(v_as_173_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1(lean_object* v_a_179_, lean_object* v_as_180_, lean_object* v_as_x27_181_, lean_object* v_b_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_List_forIn_x27_loop___at___00main_spec__1___redArg(v_a_179_, v_as_x27_181_, v_b_182_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__1___boxed(lean_object* v_a_186_, lean_object* v_as_187_, lean_object* v_as_x27_188_, lean_object* v_b_189_, lean_object* v_a_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_List_forIn_x27_loop___at___00main_spec__1(v_a_186_, v_as_187_, v_as_x27_188_, v_b_189_, v_a_190_);
lean_dec(v_as_x27_188_);
lean_dec(v_as_187_);
return v_res_192_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_Replay(uint8_t builtin);
lean_object* initialize_Lean_Util_Path(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Diagnostic(uint8_t builtin) {
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
    return _lean_main();
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  res = initialize_Diagnostic(1 /* builtin */);
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
