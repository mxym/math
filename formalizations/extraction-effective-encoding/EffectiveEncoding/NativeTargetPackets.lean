import EffectiveEncoding.NativeTargetAngles

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding


def nativePhaseCosExpression (a b : NativeAngleInput) (p : ℕ) : NativeScalarExpression :=
  .add (.mul ((a.half 1).cosExpression (p+3)) ((b.half 1).cosExpression (p+3)))
    (.mul ((a.half 1).sinExpression (p+3)) ((b.half 1).sinExpression (p+3)))


def nativePhaseSinExpression (a b : NativeAngleInput) (p : ℕ) : NativeScalarExpression :=
  .add (.mul ((a.half 1).sinExpression (p+3)) ((b.half 1).cosExpression (p+3)))
    (.neg (.mul ((a.half 1).cosExpression (p+3)) ((b.half 1).sinExpression (p+3))))


theorem nativePhaseCosExpression_decode (a b : AngleCode) (p : ℕ) :
    (nativePhaseCosExpression (prepareNativeAngleInput a) (prepareNativeAngleInput b) p).wordRun.value.decode=
      rawPhaseCos a b p := by
  simp only [nativePhaseCosExpression,NativeScalarExpression.wordRun,wordScalarAddProgram_decode,
    wordScalarMultiplyProgram_decode,←prepareNativeAngleInput_half,
    prepareNativeAngleInput_cos_decode,prepareNativeAngleInput_sin_decode,rawPhaseCos]


theorem nativePhaseSinExpression_decode (a b : AngleCode) (p : ℕ) :
    (nativePhaseSinExpression (prepareNativeAngleInput a) (prepareNativeAngleInput b) p).wordRun.value.decode=
      rawPhaseSin a b p := by
  simp only [nativePhaseSinExpression,NativeScalarExpression.wordRun,wordScalarAddProgram_decode,
    wordScalarMultiplyProgram_decode,wordScalarNegateProgram_decode,←prepareNativeAngleInput_half,
    prepareNativeAngleInput_cos_decode,prepareNativeAngleInput_sin_decode,rawPhaseSin]

/-- Actual native target expression, using only fixed Boolean literals and
already prepared dynamic Boolean fraction payloads. -/
def NativeSingleInput.packetExpression : NativeSingleInput → NativePacketExpressionOracle
  | .hadamard,p => .tuple ![.literal wordScalarZero,.neg (.sqrt (.literal wordScalarHalf) (p+1)),
      .literal wordScalarZero,.neg (.sqrt (.literal wordScalarHalf) (p+1))]
  | .yBasis,_ => .tuple ![.literal wordScalarHalf,.literal wordScalarHalf,.literal wordScalarHalf,.literal wordScalarHalf]
  | .phase a b,p => .tuple ![nativePhaseCosExpression a b p,nativePhaseSinExpression a b p,
      .literal wordScalarZero,.literal wordScalarZero]
  | .inverse u,p => .inverse (u.packetExpression p)


def NativeSingleInput.packetProgram (u : NativeSingleInput) (p : ℕ) : PacketWordEvaluation :=
  (u.packetExpression p).wordRun


theorem prepareNativeSingleInput_packet_decode (u : SingleCode) (p : ℕ) :
    ((prepareNativeSingleInput u).packetProgram p).value.decode=u.rawPacket p := by
  induction u with
  | hadamard =>
    simp only [prepareNativeSingleInput,NativeSingleInput.packetProgram,NativeSingleInput.packetExpression,
      NativePacketExpression.wordRun,wordPacketTupleProgram_decode,List.Vector.get_map,List.Vector.get_ofFn,
      SingleCode.rawPacket]
    apply congrArg IntegerPacket.ofScalars
    funext i
    fin_cases i <;> simp [NativeScalarExpression.wordRun,wordScalarNegateProgram_decode,
      wordScalarRootProgram_decode,nativeWordZero_decode,wordScalarHalf_decode,IntegerScalar.binaryRoot_eq,integerHalf,IntegerScalar.inv,IntegerScalar.ofInt,show Int.sign (2:ℤ)=1 by decide]
  | yBasis =>
    simp only [prepareNativeSingleInput,NativeSingleInput.packetProgram,NativeSingleInput.packetExpression,
      NativePacketExpression.wordRun,wordPacketTupleProgram_decode,List.Vector.get_map,List.Vector.get_ofFn,
      SingleCode.rawPacket]
    apply congrArg IntegerPacket.ofScalars
    funext i
    fin_cases i <;> exact wordScalarHalf_decode
  | phase a b =>
    simp only [prepareNativeSingleInput,NativeSingleInput.packetProgram,NativeSingleInput.packetExpression,
      NativePacketExpression.wordRun,wordPacketTupleProgram_decode,List.Vector.get_map,List.Vector.get_ofFn,
      SingleCode.rawPacket]
    apply congrArg IntegerPacket.ofScalars
    funext i
    fin_cases i
    · exact nativePhaseCosExpression_decode a b p
    · exact nativePhaseSinExpression_decode a b p
    · exact nativeWordZero_decode
    · exact nativeWordZero_decode
  | inverse u ih =>
    simp only [prepareNativeSingleInput,NativeSingleInput.packetProgram,NativeSingleInput.packetExpression,
      NativePacketExpression.wordRun,wordPacketInverseProgram_decode,SingleCode.rawPacket]
    exact congrArg IntegerPacket.inverse ih

/-- The caller prepares the SingleCode once, then the cache uses this native
word-valued oracle directly. There is no Rat/host-integer payload roundtrip. -/
def NativeSingleInput.packetDataOracle (u : NativeSingleInput) : ℕ → WordIntegerPacket :=
  fun p => (u.packetProgram p).value


theorem prepareNativeSingleInput_packet_height {k : ℕ} {wire : Fin (originalWireCount k)}
    {u : SingleCode} (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word) (p : ℕ) :
    IntegerPacketHeight ((prepareNativeSingleInput u).packetDataOracle p).decode
      (1000000*(k+3)^7*(p+5)) := by
  rw [NativeSingleInput.packetDataOracle,prepareNativeSingleInput_packet_decode]
  rw [preparedNativeDescriptorRun_eq,nativeDescriptorRun_actualWord] at hu
  exact extractionCode_rawPacket_height hu p

end EffectiveEncoding
