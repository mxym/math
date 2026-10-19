import CircuitNumerical.PacketMachineFixtures

open Lean

run_cmd do
  let names : List Lean.Name := [
    ``CircuitRecursion.NativeQueryMachine.readerStacks_read,
    ``CircuitRecursion.NativeQueryMachine.readerStacks_update,
    ``CircuitRecursion.NativeQueryMachine.compileReader_stepAux,
    ``CircuitRecursion.NativeQueryMachine.reader_step,
    ``CircuitRecursion.NativeQueryMachine.readerRun_steps,
    ``CircuitRecursion.NativeQueryMachine.compileReader_statementDepth,
    ``CircuitRecursion.NativeQueryMachine.parserStacks_input,
    ``CircuitRecursion.NativeQueryMachine.parserStacks_scratch,
    ``CircuitRecursion.NativeQueryMachine.parserStacks_numerator,
    ``CircuitRecursion.NativeQueryMachine.parserStacks_denominator,
    ``CircuitRecursion.NativeQueryMachine.parserStacks_update_input,
    ``CircuitRecursion.NativeQueryMachine.parserStacks_update_scratch,
    ``CircuitRecursion.NativeQueryMachine.parserStacks_update_numerator,
    ``CircuitRecursion.NativeQueryMachine.parserStacks_update_denominator,
    ``CircuitRecursion.NativeQueryMachine.compileParser_stepAux,
    ``CircuitRecursion.NativeQueryMachine.parser_step,
    ``CircuitRecursion.NativeQueryMachine.compileParser_statementDepth,
    ``CircuitRecursion.NativeQueryMachine.readerStacks_word_update,
    ``CircuitRecursion.NativeQueryMachine.words_update_self,
    ``CircuitRecursion.NativeQueryMachine.words_update_twice,
    ``CircuitRecursion.NativeQueryMachine.clearFinishMemory_withCell,
    ``CircuitRecursion.NativeQueryMachine.clear_word_nil,
    ``CircuitRecursion.NativeQueryMachine.clear_word_cons,
    ``CircuitRecursion.NativeQueryMachine.clearWord_iterate_override,
    ``CircuitRecursion.NativeQueryMachine.clearWord_iterate,
    ``CircuitRecursion.NativeQueryMachine.clearAll_iterate,
    ``CircuitRecursion.NativeQueryMachine.clearRun_steps,
    ``CircuitRecursion.NativeQueryMachine.clear_to_reader,
    ``CircuitRecursion.NativeQueryMachine.record_terminal_memory,
    ``CircuitRecursion.NativeQueryMachine.query_terminal_memory,
    ``CircuitRecursion.NativeQueryMachine.reader_to_parser,
    ``CircuitRecursion.NativeQueryMachine.nativeQueryRun_steps,
    ``CircuitRecursion.NativeQueryMachine.addressed_mem,
    ``CircuitRecursion.NativeQueryMachine.nativeQueryRun_steps_height,
    ``CircuitRecursion.NativeQueryMachine.parserStacks_other,
    ``CircuitRecursion.NativeQueryMachine.resultRaw_terminal,
    ``CircuitRecursion.NativeQueryMachine.typed_result,
    ``CircuitRecursion.NativeQueryMachine.terminal_master,
    ``CircuitRecursion.NativeQueryMachine.terminal_queries,
    ``CircuitRecursion.NativeQueryMachine.terminal_cache_tail,
    ``CircuitRecursion.NativeQueryMachine.terminal_symbol_scratch,
    ``CircuitRecursion.NativeQueryMachine.terminal_symbol_payload_consumed,
    ``CircuitRecursion.NativeQueryMachine.terminal_native_scratch,
    ``CircuitRecursion.NativeQueryMachine.terminal_accepted,
    ``CircuitRecursion.NativeQueryMachine.terminal_halts,
    ``CircuitRecursion.NativeQueryMachine.nativeQuery_mem_eval,
    ``CircuitRecursion.NativeQueryMachine.terminal_wordVolume,
    ``CircuitRecursion.NativeQueryMachine.terminal_wordVolume_height,
    ``CircuitRecursion.NativeQueryMachine.program_supports,
    ``CircuitRecursion.NativeQueryMachine.stack_card,
    ``CircuitRecursion.NativeQueryMachine.running_control_card,
    ``CircuitRecursion.NativeQueryMachine.statement_depth,
    ``CircuitRecursion.NativeQueryMachine.encodeCache_drop_length,
    ``CircuitRecursion.NativeQueryMachine.terminal_symbolVolume,
    ``CircuitRecursion.NativeQueryMachine.reentry_memory,
    ``CircuitRecursion.NativeQueryMachine.reentry_stacks,
    ``CircuitRecursion.NativeQueryMachine.returned_reentry,
    ``CircuitRecursion.NativeQueryMachine.alphabet_card_bound,
    ``CircuitRecursion.PacketSerializerMachine.clear_nil,
    ``CircuitRecursion.PacketSerializerMachine.clear_cons,
    ``CircuitRecursion.PacketSerializerMachine.start_step,
    ``CircuitRecursion.PacketSerializerMachine.denRead_nil,
    ``CircuitRecursion.PacketSerializerMachine.denRead_cons,
    ``CircuitRecursion.PacketSerializerMachine.denWrite_nil,
    ``CircuitRecursion.PacketSerializerMachine.denWrite_cons,
    ``CircuitRecursion.PacketSerializerMachine.beginNum_step,
    ``CircuitRecursion.PacketSerializerMachine.readNum_nil,
    ``CircuitRecursion.PacketSerializerMachine.readNum_cons,
    ``CircuitRecursion.PacketSerializerMachine.writeNum_nil,
    ``CircuitRecursion.PacketSerializerMachine.writeNum_cons,
    ``CircuitRecursion.PacketSerializerMachine.finishNum_step,
    ``CircuitRecursion.PacketSerializerMachine.clear_iterate,
    ``CircuitRecursion.PacketSerializerMachine.denRead_iterate,
    ``CircuitRecursion.PacketSerializerMachine.denWrite_iterate,
    ``CircuitRecursion.PacketSerializerMachine.readNum_iterate_override,
    ``CircuitRecursion.PacketSerializerMachine.writeNum_iterate,
    ``CircuitRecursion.PacketSerializerMachine.denominator_iterate,
    ``CircuitRecursion.PacketSerializerMachine.readWriteNum_iterate,
    ``CircuitRecursion.PacketSerializerMachine.numerator_iterate_override,
    ``CircuitRecursion.PacketSerializerMachine.numerator_iterate,
    ``CircuitRecursion.PacketSerializerMachine.fresh_iterate,
    ``CircuitRecursion.PacketSerializerMachine.serialize_iterate,
    ``CircuitRecursion.PacketSerializerMachine.serializeRun_steps,
    ``CircuitRecursion.PacketSerializerMachine.serializeTime_encoded_length,
    ``CircuitRecursion.PacketSerializerMachine.serializePacketRun_steps_height,
    ``CircuitRecursion.PacketSerializerMachine.terminal_encoded,
    ``CircuitRecursion.PacketSerializerMachine.terminal_empty_fields,
    ``CircuitRecursion.PacketSerializerMachine.terminal_empty_denominator,
    ``CircuitRecursion.PacketSerializerMachine.terminal_empty_scratch,
    ``CircuitRecursion.PacketSerializerMachine.serialized_decode,
    ``CircuitRecursion.PacketSerializerMachine.terminal_halts,
    ``CircuitRecursion.PacketSerializerMachine.serialize_mem_eval,
    ``CircuitRecursion.PacketSerializerMachine.program_supports,
    ``CircuitRecursion.PacketSerializerMachine.running_control_card,
    ``CircuitRecursion.PacketSerializerMachine.statement_depth,
    ``CircuitRecursion.PacketCodecMachine.parser_to_serializer,
    ``CircuitRecursion.PacketCodecMachine.finish_step,
    ``CircuitRecursion.PacketCodecMachine.codecRun_steps,
    ``CircuitRecursion.PacketCodecMachine.codecTime_encoded_length,
    ``CircuitRecursion.PacketCodecMachine.codecRun_steps_height,
    ``CircuitRecursion.PacketCodecMachine.intermediate_native_exact,
    ``CircuitRecursion.PacketCodecMachine.terminal_encoded_exact,
    ``CircuitRecursion.PacketCodecMachine.terminal_numerators_empty,
    ``CircuitRecursion.PacketCodecMachine.terminal_denominator_empty,
    ``CircuitRecursion.PacketCodecMachine.terminal_scratch_empty,
    ``CircuitRecursion.PacketCodecMachine.terminal_halts,
    ``CircuitRecursion.PacketCodecMachine.codec_mem_eval,
    ``CircuitRecursion.PacketCodecMachine.program_supports,
    ``CircuitRecursion.PacketCodecMachine.running_control_card,
    ``CircuitRecursion.PacketCodecMachine.statement_depth,
    ``CircuitRecursion.PacketMachineFixtures.valid0,
    ``CircuitRecursion.PacketMachineFixtures.valid1,
    ``CircuitRecursion.PacketMachineFixtures.nativeStacks_complete,
    ``CircuitRecursion.PacketMachineFixtures.fieldStacks_complete]
  let env ← getEnv
  for n in names do
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError m!"STRICT_DECL_KIND_FAIL expected theorem {n}"
  logInfo m!"STRICT_DECL_KIND_PASS theorem count={names.length}"

run_cmd do
  let names : List Lean.Name := [
    ``CircuitRecursion.NativeQueryMachine.Stack,
    ``CircuitRecursion.NativeQueryMachine.Alphabet,
    ``CircuitRecursion.NativeQueryMachine.Memory,
    ``CircuitRecursion.NativeQueryMachine.readerStacks,
    ``CircuitRecursion.NativeQueryMachine.readerConfiguration,
    ``CircuitRecursion.NativeQueryMachine.compileReader,
    ``CircuitRecursion.NativeQueryMachine.readerProgram,
    ``CircuitRecursion.NativeQueryMachine.readerRun,
    ``CircuitRecursion.NativeQueryMachine.inputStack,
    ``CircuitRecursion.NativeQueryMachine.parserStacks,
    ``CircuitRecursion.NativeQueryMachine.parserConfiguration,
    ``CircuitRecursion.NativeQueryMachine.compileParser,
    ``CircuitRecursion.NativeQueryMachine.parserRun,
    ``CircuitRecursion.NativeQueryMachine.Label,
    ``CircuitRecursion.NativeQueryMachine.Configuration,
    ``CircuitRecursion.NativeQueryMachine.readerEmbed,
    ``CircuitRecursion.NativeQueryMachine.parserEmbed,
    ``CircuitRecursion.NativeQueryMachine.readerReturn,
    ``CircuitRecursion.NativeQueryMachine.resetMemory,
    ``CircuitRecursion.NativeQueryMachine.clearNext,
    ``CircuitRecursion.NativeQueryMachine.clearFinishMemory,
    ``CircuitRecursion.NativeQueryMachine.program,
    ``CircuitRecursion.NativeQueryMachine.configuration,
    ``CircuitRecursion.NativeQueryMachine.advance,
    ``CircuitRecursion.NativeQueryMachine.emptyWords,
    ``CircuitRecursion.NativeQueryMachine.wordVolume,
    ``CircuitRecursion.NativeQueryMachine.clearRun,
    ``CircuitRecursion.NativeQueryMachine.sourceInitial,
    ``CircuitRecursion.NativeQueryMachine.initial,
    ``CircuitRecursion.NativeQueryMachine.readerCall,
    ``CircuitRecursion.NativeQueryMachine.terminal,
    ``CircuitRecursion.NativeQueryMachine.selectedParserCall,
    ``CircuitRecursion.NativeQueryMachine.nativeQueryRun,
    ``CircuitRecursion.NativeQueryMachine.resultRaw,
    ``CircuitRecursion.NativeQueryMachine.nativeWords,
    ``CircuitRecursion.NativeQueryMachine.nativeQueryCall,
    ``CircuitRecursion.NativeQueryMachine.symbolVolume,
    ``CircuitRecursion.NativeQueryMachine.reentry,
    ``CircuitRecursion.NativeQueryMachine.reuseRun,
    ``CircuitRecursion.PacketSerializerMachine.Stack,
    ``CircuitRecursion.PacketSerializerMachine.Alphabet,
    ``CircuitRecursion.PacketSerializerMachine.Coordinate,
    ``CircuitRecursion.PacketSerializerMachine.Memory,
    ``CircuitRecursion.PacketSerializerMachine.Flags,
    ``CircuitRecursion.PacketSerializerMachine.Configuration,
    ``CircuitRecursion.PacketSerializerMachine.configuration,
    ``CircuitRecursion.PacketSerializerMachine.signBit,
    ``CircuitRecursion.PacketSerializerMachine.next,
    ``CircuitRecursion.PacketSerializerMachine.finish,
    ``CircuitRecursion.PacketSerializerMachine.program,
    ``CircuitRecursion.PacketSerializerMachine.advance,
    ``CircuitRecursion.PacketSerializerMachine.freshTime,
    ``CircuitRecursion.PacketSerializerMachine.serializeTime,
    ``CircuitRecursion.PacketSerializerMachine.terminal,
    ``CircuitRecursion.PacketSerializerMachine.serializeRun,
    ``CircuitRecursion.PacketSerializerMachine.serializePacketRun,
    ``CircuitRecursion.PacketSerializerMachine.serializeCall,
    ``CircuitRecursion.PacketCodecMachine.Alphabet,
    ``CircuitRecursion.PacketCodecMachine.Memory,
    ``CircuitRecursion.PacketCodecMachine.Label,
    ``CircuitRecursion.PacketCodecMachine.Configuration,
    ``CircuitRecursion.PacketCodecMachine.parserEmbed,
    ``CircuitRecursion.PacketCodecMachine.parserReturn,
    ``CircuitRecursion.PacketCodecMachine.serializerEmbed,
    ``CircuitRecursion.PacketCodecMachine.serializerReturn,
    ``CircuitRecursion.PacketCodecMachine.program,
    ``CircuitRecursion.PacketCodecMachine.advance,
    ``CircuitRecursion.PacketCodecMachine.initial,
    ``CircuitRecursion.PacketCodecMachine.intermediate,
    ``CircuitRecursion.PacketCodecMachine.terminal,
    ``CircuitRecursion.PacketCodecMachine.codecTime,
    ``CircuitRecursion.PacketCodecMachine.parserCall,
    ``CircuitRecursion.PacketCodecMachine.serializerCall,
    ``CircuitRecursion.PacketCodecMachine.codecRun,
    ``CircuitRecursion.PacketCodecMachine.observedNative,
    ``CircuitRecursion.PacketMachineFixtures.raw0,
    ``CircuitRecursion.PacketMachineFixtures.raw1,
    ``CircuitRecursion.PacketMachineFixtures.packet0,
    ``CircuitRecursion.PacketMachineFixtures.packet1,
    ``CircuitRecursion.PacketMachineFixtures.index0,
    ``CircuitRecursion.PacketMachineFixtures.index1,
    ``CircuitRecursion.PacketMachineFixtures.oldIndex,
    ``CircuitRecursion.PacketMachineFixtures.oldScratch,
    ``CircuitRecursion.PacketMachineFixtures.oldCache,
    ``CircuitRecursion.PacketMachineFixtures.queryTail,
    ``CircuitRecursion.PacketMachineFixtures.oldMemory,
    ``CircuitRecursion.PacketMachineFixtures.oldWords,
    ``CircuitRecursion.PacketMachineFixtures.packetFlags,
    ``CircuitRecursion.PacketMachineFixtures.packetWords,
    ``CircuitRecursion.PacketMachineFixtures.expectedNative,
    ``CircuitRecursion.PacketMachineFixtures.nativeStacks,
    ``CircuitRecursion.PacketMachineFixtures.sameNative,
    ``CircuitRecursion.PacketMachineFixtures.execute,
    ``CircuitRecursion.PacketMachineFixtures.assertNative,
    ``CircuitRecursion.PacketMachineFixtures.DriverLabel,
    ``CircuitRecursion.PacketMachineFixtures.DriverConfiguration,
    ``CircuitRecursion.PacketMachineFixtures.driverEmbed,
    ``CircuitRecursion.PacketMachineFixtures.driverReturn,
    ``CircuitRecursion.PacketMachineFixtures.driverProgram,
    ``CircuitRecursion.PacketMachineFixtures.assertTwoNative,
    ``CircuitRecursion.PacketMachineFixtures.fieldStacks,
    ``CircuitRecursion.PacketMachineFixtures.sameFields,
    ``CircuitRecursion.PacketMachineFixtures.assertSerializer,
    ``CircuitRecursion.PacketMachineFixtures.assertCodec]
  let env ← getEnv
  for n in names do
    match env.find? n with
    | some (.defnInfo _) => pure ()
    | _ => throwError m!"STRICT_DECL_KIND_FAIL expected definition {n}"
  logInfo m!"STRICT_DECL_KIND_PASS definition count={names.length}"

run_cmd do
  let names : List Lean.Name := [
    ``CircuitRecursion.NativeQueryMachine.WordStack,
    ``CircuitRecursion.PacketSerializerMachine.Label]
  let env ← getEnv
  for n in names do
    match env.find? n with
    | some (.inductInfo _) => pure ()
    | _ => throwError m!"STRICT_DECL_KIND_FAIL expected inductive {n}"
  logInfo m!"STRICT_DECL_KIND_PASS inductive count={names.length}"

#check CircuitRecursion.NativeQueryMachine.readerStacks_read
#print axioms CircuitRecursion.NativeQueryMachine.readerStacks_read
#check CircuitRecursion.NativeQueryMachine.readerStacks_update
#print axioms CircuitRecursion.NativeQueryMachine.readerStacks_update
#check CircuitRecursion.NativeQueryMachine.compileReader_stepAux
#print axioms CircuitRecursion.NativeQueryMachine.compileReader_stepAux
#check CircuitRecursion.NativeQueryMachine.reader_step
#print axioms CircuitRecursion.NativeQueryMachine.reader_step
#check CircuitRecursion.NativeQueryMachine.readerRun_steps
#print axioms CircuitRecursion.NativeQueryMachine.readerRun_steps
#check CircuitRecursion.NativeQueryMachine.compileReader_statementDepth
#print axioms CircuitRecursion.NativeQueryMachine.compileReader_statementDepth
#check CircuitRecursion.NativeQueryMachine.parserStacks_input
#print axioms CircuitRecursion.NativeQueryMachine.parserStacks_input
#check CircuitRecursion.NativeQueryMachine.parserStacks_scratch
#print axioms CircuitRecursion.NativeQueryMachine.parserStacks_scratch
#check CircuitRecursion.NativeQueryMachine.parserStacks_numerator
#print axioms CircuitRecursion.NativeQueryMachine.parserStacks_numerator
#check CircuitRecursion.NativeQueryMachine.parserStacks_denominator
#print axioms CircuitRecursion.NativeQueryMachine.parserStacks_denominator
#check CircuitRecursion.NativeQueryMachine.parserStacks_update_input
#print axioms CircuitRecursion.NativeQueryMachine.parserStacks_update_input
#check CircuitRecursion.NativeQueryMachine.parserStacks_update_scratch
#print axioms CircuitRecursion.NativeQueryMachine.parserStacks_update_scratch
#check CircuitRecursion.NativeQueryMachine.parserStacks_update_numerator
#print axioms CircuitRecursion.NativeQueryMachine.parserStacks_update_numerator
#check CircuitRecursion.NativeQueryMachine.parserStacks_update_denominator
#print axioms CircuitRecursion.NativeQueryMachine.parserStacks_update_denominator
#check CircuitRecursion.NativeQueryMachine.compileParser_stepAux
#print axioms CircuitRecursion.NativeQueryMachine.compileParser_stepAux
#check CircuitRecursion.NativeQueryMachine.parser_step
#print axioms CircuitRecursion.NativeQueryMachine.parser_step
#check CircuitRecursion.NativeQueryMachine.compileParser_statementDepth
#print axioms CircuitRecursion.NativeQueryMachine.compileParser_statementDepth
#check CircuitRecursion.NativeQueryMachine.readerStacks_word_update
#print axioms CircuitRecursion.NativeQueryMachine.readerStacks_word_update
#check CircuitRecursion.NativeQueryMachine.words_update_self
#print axioms CircuitRecursion.NativeQueryMachine.words_update_self
#check CircuitRecursion.NativeQueryMachine.words_update_twice
#print axioms CircuitRecursion.NativeQueryMachine.words_update_twice
#check CircuitRecursion.NativeQueryMachine.clearFinishMemory_withCell
#print axioms CircuitRecursion.NativeQueryMachine.clearFinishMemory_withCell
#check CircuitRecursion.NativeQueryMachine.clear_word_nil
#print axioms CircuitRecursion.NativeQueryMachine.clear_word_nil
#check CircuitRecursion.NativeQueryMachine.clear_word_cons
#print axioms CircuitRecursion.NativeQueryMachine.clear_word_cons
#check CircuitRecursion.NativeQueryMachine.clearWord_iterate_override
#print axioms CircuitRecursion.NativeQueryMachine.clearWord_iterate_override
#check CircuitRecursion.NativeQueryMachine.clearWord_iterate
#print axioms CircuitRecursion.NativeQueryMachine.clearWord_iterate
#check CircuitRecursion.NativeQueryMachine.clearAll_iterate
#print axioms CircuitRecursion.NativeQueryMachine.clearAll_iterate
#check CircuitRecursion.NativeQueryMachine.clearRun_steps
#print axioms CircuitRecursion.NativeQueryMachine.clearRun_steps
#check CircuitRecursion.NativeQueryMachine.clear_to_reader
#print axioms CircuitRecursion.NativeQueryMachine.clear_to_reader
#check CircuitRecursion.NativeQueryMachine.record_terminal_memory
#print axioms CircuitRecursion.NativeQueryMachine.record_terminal_memory
#check CircuitRecursion.NativeQueryMachine.query_terminal_memory
#print axioms CircuitRecursion.NativeQueryMachine.query_terminal_memory
#check CircuitRecursion.NativeQueryMachine.reader_to_parser
#print axioms CircuitRecursion.NativeQueryMachine.reader_to_parser
#check CircuitRecursion.NativeQueryMachine.nativeQueryRun_steps
#print axioms CircuitRecursion.NativeQueryMachine.nativeQueryRun_steps
#check CircuitRecursion.NativeQueryMachine.addressed_mem
#print axioms CircuitRecursion.NativeQueryMachine.addressed_mem
#check CircuitRecursion.NativeQueryMachine.nativeQueryRun_steps_height
#print axioms CircuitRecursion.NativeQueryMachine.nativeQueryRun_steps_height
#check CircuitRecursion.NativeQueryMachine.parserStacks_other
#print axioms CircuitRecursion.NativeQueryMachine.parserStacks_other
#check CircuitRecursion.NativeQueryMachine.resultRaw_terminal
#print axioms CircuitRecursion.NativeQueryMachine.resultRaw_terminal
#check CircuitRecursion.NativeQueryMachine.typed_result
#print axioms CircuitRecursion.NativeQueryMachine.typed_result
#check CircuitRecursion.NativeQueryMachine.terminal_master
#print axioms CircuitRecursion.NativeQueryMachine.terminal_master
#check CircuitRecursion.NativeQueryMachine.terminal_queries
#print axioms CircuitRecursion.NativeQueryMachine.terminal_queries
#check CircuitRecursion.NativeQueryMachine.terminal_cache_tail
#print axioms CircuitRecursion.NativeQueryMachine.terminal_cache_tail
#check CircuitRecursion.NativeQueryMachine.terminal_symbol_scratch
#print axioms CircuitRecursion.NativeQueryMachine.terminal_symbol_scratch
#check CircuitRecursion.NativeQueryMachine.terminal_symbol_payload_consumed
#print axioms CircuitRecursion.NativeQueryMachine.terminal_symbol_payload_consumed
#check CircuitRecursion.NativeQueryMachine.terminal_native_scratch
#print axioms CircuitRecursion.NativeQueryMachine.terminal_native_scratch
#check CircuitRecursion.NativeQueryMachine.terminal_accepted
#print axioms CircuitRecursion.NativeQueryMachine.terminal_accepted
#check CircuitRecursion.NativeQueryMachine.terminal_halts
#print axioms CircuitRecursion.NativeQueryMachine.terminal_halts
#check CircuitRecursion.NativeQueryMachine.nativeQuery_mem_eval
#print axioms CircuitRecursion.NativeQueryMachine.nativeQuery_mem_eval
#check CircuitRecursion.NativeQueryMachine.terminal_wordVolume
#print axioms CircuitRecursion.NativeQueryMachine.terminal_wordVolume
#check CircuitRecursion.NativeQueryMachine.terminal_wordVolume_height
#print axioms CircuitRecursion.NativeQueryMachine.terminal_wordVolume_height
#check CircuitRecursion.NativeQueryMachine.program_supports
#print axioms CircuitRecursion.NativeQueryMachine.program_supports
#check CircuitRecursion.NativeQueryMachine.stack_card
#print axioms CircuitRecursion.NativeQueryMachine.stack_card
#check CircuitRecursion.NativeQueryMachine.running_control_card
#print axioms CircuitRecursion.NativeQueryMachine.running_control_card
#check CircuitRecursion.NativeQueryMachine.statement_depth
#print axioms CircuitRecursion.NativeQueryMachine.statement_depth
#check CircuitRecursion.NativeQueryMachine.encodeCache_drop_length
#print axioms CircuitRecursion.NativeQueryMachine.encodeCache_drop_length
#check CircuitRecursion.NativeQueryMachine.terminal_symbolVolume
#print axioms CircuitRecursion.NativeQueryMachine.terminal_symbolVolume
#check CircuitRecursion.NativeQueryMachine.reentry_memory
#print axioms CircuitRecursion.NativeQueryMachine.reentry_memory
#check CircuitRecursion.NativeQueryMachine.reentry_stacks
#print axioms CircuitRecursion.NativeQueryMachine.reentry_stacks
#check CircuitRecursion.NativeQueryMachine.returned_reentry
#print axioms CircuitRecursion.NativeQueryMachine.returned_reentry
#check CircuitRecursion.NativeQueryMachine.alphabet_card_bound
#print axioms CircuitRecursion.NativeQueryMachine.alphabet_card_bound
#check CircuitRecursion.PacketSerializerMachine.clear_nil
#print axioms CircuitRecursion.PacketSerializerMachine.clear_nil
#check CircuitRecursion.PacketSerializerMachine.clear_cons
#print axioms CircuitRecursion.PacketSerializerMachine.clear_cons
#check CircuitRecursion.PacketSerializerMachine.start_step
#print axioms CircuitRecursion.PacketSerializerMachine.start_step
#check CircuitRecursion.PacketSerializerMachine.denRead_nil
#print axioms CircuitRecursion.PacketSerializerMachine.denRead_nil
#check CircuitRecursion.PacketSerializerMachine.denRead_cons
#print axioms CircuitRecursion.PacketSerializerMachine.denRead_cons
#check CircuitRecursion.PacketSerializerMachine.denWrite_nil
#print axioms CircuitRecursion.PacketSerializerMachine.denWrite_nil
#check CircuitRecursion.PacketSerializerMachine.denWrite_cons
#print axioms CircuitRecursion.PacketSerializerMachine.denWrite_cons
#check CircuitRecursion.PacketSerializerMachine.beginNum_step
#print axioms CircuitRecursion.PacketSerializerMachine.beginNum_step
#check CircuitRecursion.PacketSerializerMachine.readNum_nil
#print axioms CircuitRecursion.PacketSerializerMachine.readNum_nil
#check CircuitRecursion.PacketSerializerMachine.readNum_cons
#print axioms CircuitRecursion.PacketSerializerMachine.readNum_cons
#check CircuitRecursion.PacketSerializerMachine.writeNum_nil
#print axioms CircuitRecursion.PacketSerializerMachine.writeNum_nil
#check CircuitRecursion.PacketSerializerMachine.writeNum_cons
#print axioms CircuitRecursion.PacketSerializerMachine.writeNum_cons
#check CircuitRecursion.PacketSerializerMachine.finishNum_step
#print axioms CircuitRecursion.PacketSerializerMachine.finishNum_step
#check CircuitRecursion.PacketSerializerMachine.clear_iterate
#print axioms CircuitRecursion.PacketSerializerMachine.clear_iterate
#check CircuitRecursion.PacketSerializerMachine.denRead_iterate
#print axioms CircuitRecursion.PacketSerializerMachine.denRead_iterate
#check CircuitRecursion.PacketSerializerMachine.denWrite_iterate
#print axioms CircuitRecursion.PacketSerializerMachine.denWrite_iterate
#check CircuitRecursion.PacketSerializerMachine.readNum_iterate_override
#print axioms CircuitRecursion.PacketSerializerMachine.readNum_iterate_override
#check CircuitRecursion.PacketSerializerMachine.writeNum_iterate
#print axioms CircuitRecursion.PacketSerializerMachine.writeNum_iterate
#check CircuitRecursion.PacketSerializerMachine.denominator_iterate
#print axioms CircuitRecursion.PacketSerializerMachine.denominator_iterate
#check CircuitRecursion.PacketSerializerMachine.readWriteNum_iterate
#print axioms CircuitRecursion.PacketSerializerMachine.readWriteNum_iterate
#check CircuitRecursion.PacketSerializerMachine.numerator_iterate_override
#print axioms CircuitRecursion.PacketSerializerMachine.numerator_iterate_override
#check CircuitRecursion.PacketSerializerMachine.numerator_iterate
#print axioms CircuitRecursion.PacketSerializerMachine.numerator_iterate
#check CircuitRecursion.PacketSerializerMachine.fresh_iterate
#print axioms CircuitRecursion.PacketSerializerMachine.fresh_iterate
#check CircuitRecursion.PacketSerializerMachine.serialize_iterate
#print axioms CircuitRecursion.PacketSerializerMachine.serialize_iterate
#check CircuitRecursion.PacketSerializerMachine.serializeRun_steps
#print axioms CircuitRecursion.PacketSerializerMachine.serializeRun_steps
#check CircuitRecursion.PacketSerializerMachine.serializeTime_encoded_length
#print axioms CircuitRecursion.PacketSerializerMachine.serializeTime_encoded_length
#check CircuitRecursion.PacketSerializerMachine.serializePacketRun_steps_height
#print axioms CircuitRecursion.PacketSerializerMachine.serializePacketRun_steps_height
#check CircuitRecursion.PacketSerializerMachine.terminal_encoded
#print axioms CircuitRecursion.PacketSerializerMachine.terminal_encoded
#check CircuitRecursion.PacketSerializerMachine.terminal_empty_fields
#print axioms CircuitRecursion.PacketSerializerMachine.terminal_empty_fields
#check CircuitRecursion.PacketSerializerMachine.terminal_empty_denominator
#print axioms CircuitRecursion.PacketSerializerMachine.terminal_empty_denominator
#check CircuitRecursion.PacketSerializerMachine.terminal_empty_scratch
#print axioms CircuitRecursion.PacketSerializerMachine.terminal_empty_scratch
#check CircuitRecursion.PacketSerializerMachine.serialized_decode
#print axioms CircuitRecursion.PacketSerializerMachine.serialized_decode
#check CircuitRecursion.PacketSerializerMachine.terminal_halts
#print axioms CircuitRecursion.PacketSerializerMachine.terminal_halts
#check CircuitRecursion.PacketSerializerMachine.serialize_mem_eval
#print axioms CircuitRecursion.PacketSerializerMachine.serialize_mem_eval
#check CircuitRecursion.PacketSerializerMachine.program_supports
#print axioms CircuitRecursion.PacketSerializerMachine.program_supports
#check CircuitRecursion.PacketSerializerMachine.running_control_card
#print axioms CircuitRecursion.PacketSerializerMachine.running_control_card
#check CircuitRecursion.PacketSerializerMachine.statement_depth
#print axioms CircuitRecursion.PacketSerializerMachine.statement_depth
#check CircuitRecursion.PacketCodecMachine.parser_to_serializer
#print axioms CircuitRecursion.PacketCodecMachine.parser_to_serializer
#check CircuitRecursion.PacketCodecMachine.finish_step
#print axioms CircuitRecursion.PacketCodecMachine.finish_step
#check CircuitRecursion.PacketCodecMachine.codecRun_steps
#print axioms CircuitRecursion.PacketCodecMachine.codecRun_steps
#check CircuitRecursion.PacketCodecMachine.codecTime_encoded_length
#print axioms CircuitRecursion.PacketCodecMachine.codecTime_encoded_length
#check CircuitRecursion.PacketCodecMachine.codecRun_steps_height
#print axioms CircuitRecursion.PacketCodecMachine.codecRun_steps_height
#check CircuitRecursion.PacketCodecMachine.intermediate_native_exact
#print axioms CircuitRecursion.PacketCodecMachine.intermediate_native_exact
#check CircuitRecursion.PacketCodecMachine.terminal_encoded_exact
#print axioms CircuitRecursion.PacketCodecMachine.terminal_encoded_exact
#check CircuitRecursion.PacketCodecMachine.terminal_numerators_empty
#print axioms CircuitRecursion.PacketCodecMachine.terminal_numerators_empty
#check CircuitRecursion.PacketCodecMachine.terminal_denominator_empty
#print axioms CircuitRecursion.PacketCodecMachine.terminal_denominator_empty
#check CircuitRecursion.PacketCodecMachine.terminal_scratch_empty
#print axioms CircuitRecursion.PacketCodecMachine.terminal_scratch_empty
#check CircuitRecursion.PacketCodecMachine.terminal_halts
#print axioms CircuitRecursion.PacketCodecMachine.terminal_halts
#check CircuitRecursion.PacketCodecMachine.codec_mem_eval
#print axioms CircuitRecursion.PacketCodecMachine.codec_mem_eval
#check CircuitRecursion.PacketCodecMachine.program_supports
#print axioms CircuitRecursion.PacketCodecMachine.program_supports
#check CircuitRecursion.PacketCodecMachine.running_control_card
#print axioms CircuitRecursion.PacketCodecMachine.running_control_card
#check CircuitRecursion.PacketCodecMachine.statement_depth
#print axioms CircuitRecursion.PacketCodecMachine.statement_depth
#check CircuitRecursion.PacketMachineFixtures.valid0
#print axioms CircuitRecursion.PacketMachineFixtures.valid0
#check CircuitRecursion.PacketMachineFixtures.valid1
#print axioms CircuitRecursion.PacketMachineFixtures.valid1
#check CircuitRecursion.PacketMachineFixtures.nativeStacks_complete
#print axioms CircuitRecursion.PacketMachineFixtures.nativeStacks_complete
#check CircuitRecursion.PacketMachineFixtures.fieldStacks_complete
#print axioms CircuitRecursion.PacketMachineFixtures.fieldStacks_complete
#check CircuitRecursion.NativeQueryMachine.WordStack
#check CircuitRecursion.NativeQueryMachine.Stack
#check CircuitRecursion.NativeQueryMachine.Alphabet
#check CircuitRecursion.NativeQueryMachine.Memory
#check CircuitRecursion.NativeQueryMachine.readerStacks
#check CircuitRecursion.NativeQueryMachine.readerConfiguration
#check CircuitRecursion.NativeQueryMachine.compileReader
#check CircuitRecursion.NativeQueryMachine.readerProgram
#check CircuitRecursion.NativeQueryMachine.readerRun
#check CircuitRecursion.NativeQueryMachine.inputStack
#check CircuitRecursion.NativeQueryMachine.parserStacks
#check CircuitRecursion.NativeQueryMachine.parserConfiguration
#check CircuitRecursion.NativeQueryMachine.compileParser
#check CircuitRecursion.NativeQueryMachine.parserRun
#check CircuitRecursion.NativeQueryMachine.Label
#check CircuitRecursion.NativeQueryMachine.Configuration
#check CircuitRecursion.NativeQueryMachine.readerEmbed
#check CircuitRecursion.NativeQueryMachine.parserEmbed
#check CircuitRecursion.NativeQueryMachine.readerReturn
#check CircuitRecursion.NativeQueryMachine.resetMemory
#check CircuitRecursion.NativeQueryMachine.clearNext
#check CircuitRecursion.NativeQueryMachine.clearFinishMemory
#check CircuitRecursion.NativeQueryMachine.program
#check CircuitRecursion.NativeQueryMachine.configuration
#check CircuitRecursion.NativeQueryMachine.advance
#check CircuitRecursion.NativeQueryMachine.emptyWords
#check CircuitRecursion.NativeQueryMachine.wordVolume
#check CircuitRecursion.NativeQueryMachine.clearRun
#check CircuitRecursion.NativeQueryMachine.sourceInitial
#check CircuitRecursion.NativeQueryMachine.initial
#check CircuitRecursion.NativeQueryMachine.readerCall
#check CircuitRecursion.NativeQueryMachine.terminal
#check CircuitRecursion.NativeQueryMachine.selectedParserCall
#check CircuitRecursion.NativeQueryMachine.nativeQueryRun
#check CircuitRecursion.NativeQueryMachine.resultRaw
#check CircuitRecursion.NativeQueryMachine.nativeWords
#check CircuitRecursion.NativeQueryMachine.nativeQueryCall
#check CircuitRecursion.NativeQueryMachine.symbolVolume
#check CircuitRecursion.NativeQueryMachine.reentry
#check CircuitRecursion.NativeQueryMachine.reuseRun
#check CircuitRecursion.PacketSerializerMachine.Stack
#check CircuitRecursion.PacketSerializerMachine.Alphabet
#check CircuitRecursion.PacketSerializerMachine.Coordinate
#check CircuitRecursion.PacketSerializerMachine.Memory
#check CircuitRecursion.PacketSerializerMachine.Flags
#check CircuitRecursion.PacketSerializerMachine.Label
#check CircuitRecursion.PacketSerializerMachine.Configuration
#check CircuitRecursion.PacketSerializerMachine.configuration
#check CircuitRecursion.PacketSerializerMachine.signBit
#check CircuitRecursion.PacketSerializerMachine.next
#check CircuitRecursion.PacketSerializerMachine.finish
#check CircuitRecursion.PacketSerializerMachine.program
#check CircuitRecursion.PacketSerializerMachine.advance
#check CircuitRecursion.PacketSerializerMachine.freshTime
#check CircuitRecursion.PacketSerializerMachine.serializeTime
#check CircuitRecursion.PacketSerializerMachine.terminal
#check CircuitRecursion.PacketSerializerMachine.serializeRun
#check CircuitRecursion.PacketSerializerMachine.serializePacketRun
#check CircuitRecursion.PacketSerializerMachine.serializeCall
#check CircuitRecursion.PacketCodecMachine.Alphabet
#check CircuitRecursion.PacketCodecMachine.Memory
#check CircuitRecursion.PacketCodecMachine.Label
#check CircuitRecursion.PacketCodecMachine.Configuration
#check CircuitRecursion.PacketCodecMachine.parserEmbed
#check CircuitRecursion.PacketCodecMachine.parserReturn
#check CircuitRecursion.PacketCodecMachine.serializerEmbed
#check CircuitRecursion.PacketCodecMachine.serializerReturn
#check CircuitRecursion.PacketCodecMachine.program
#check CircuitRecursion.PacketCodecMachine.advance
#check CircuitRecursion.PacketCodecMachine.initial
#check CircuitRecursion.PacketCodecMachine.intermediate
#check CircuitRecursion.PacketCodecMachine.terminal
#check CircuitRecursion.PacketCodecMachine.codecTime
#check CircuitRecursion.PacketCodecMachine.parserCall
#check CircuitRecursion.PacketCodecMachine.serializerCall
#check CircuitRecursion.PacketCodecMachine.codecRun
#check CircuitRecursion.PacketCodecMachine.observedNative
#check CircuitRecursion.PacketMachineFixtures.raw0
#check CircuitRecursion.PacketMachineFixtures.raw1
#check CircuitRecursion.PacketMachineFixtures.packet0
#check CircuitRecursion.PacketMachineFixtures.packet1
#check CircuitRecursion.PacketMachineFixtures.index0
#check CircuitRecursion.PacketMachineFixtures.index1
#check CircuitRecursion.PacketMachineFixtures.oldIndex
#check CircuitRecursion.PacketMachineFixtures.oldScratch
#check CircuitRecursion.PacketMachineFixtures.oldCache
#check CircuitRecursion.PacketMachineFixtures.queryTail
#check CircuitRecursion.PacketMachineFixtures.oldMemory
#check CircuitRecursion.PacketMachineFixtures.oldWords
#check CircuitRecursion.PacketMachineFixtures.packetFlags
#check CircuitRecursion.PacketMachineFixtures.packetWords
#check CircuitRecursion.PacketMachineFixtures.expectedNative
#check CircuitRecursion.PacketMachineFixtures.nativeStacks
#check CircuitRecursion.PacketMachineFixtures.sameNative
#check CircuitRecursion.PacketMachineFixtures.execute
#check CircuitRecursion.PacketMachineFixtures.assertNative
#check CircuitRecursion.PacketMachineFixtures.DriverLabel
#check CircuitRecursion.PacketMachineFixtures.DriverConfiguration
#check CircuitRecursion.PacketMachineFixtures.driverEmbed
#check CircuitRecursion.PacketMachineFixtures.driverReturn
#check CircuitRecursion.PacketMachineFixtures.driverProgram
#check CircuitRecursion.PacketMachineFixtures.assertTwoNative
#check CircuitRecursion.PacketMachineFixtures.fieldStacks
#check CircuitRecursion.PacketMachineFixtures.sameFields
#check CircuitRecursion.PacketMachineFixtures.assertSerializer
#check CircuitRecursion.PacketMachineFixtures.assertCodec

open CircuitRecursion CircuitRecursion.PacketMachineFixtures CircuitRecursion.PacketFraming

#eval assertNative "native_one_index0_old_data" (NativeQueryMachine.initial [packet0] index0 oldMemory
  oldIndex oldScratch oldCache queryTail oldWords) (expectedNative (encodeCache [packet0]) [] queryTail packet0) 119

#eval assertNative "native_two_index0_old_data" (NativeQueryMachine.initial [packet0,packet1] index0 oldMemory
  oldIndex oldScratch oldCache queryTail oldWords)
  (expectedNative (encodeCache [packet0,packet1]) (encodeCache [packet1]) queryTail packet0) 151

#eval assertNative "native_two_index1_old_data" (NativeQueryMachine.initial [packet0,packet1] index1 oldMemory
  oldIndex oldScratch oldCache queryTail oldWords) (expectedNative (encodeCache [packet0,packet1]) [] queryTail packet1) 178

#eval assertTwoNative "native_actual_two_queries_0_then_1" index0 index1 packet0 packet1 (encodeCache [packet1]) 151 328

#eval assertTwoNative "native_actual_two_queries_1_then_0" index1 index0 packet1 packet0 [] 178 314

#eval assertSerializer

#eval assertCodec
