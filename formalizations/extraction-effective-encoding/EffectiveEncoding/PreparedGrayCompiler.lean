import EffectiveEncoding.PreparedPauliContext

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding


def preparedAdjacentSwapCode {n : ℕ} (plans : List (PreparedPauliPlan n))
    (t : Fin n) (x : Bits n) : WordCode n :=
  [.single t .hadamard]++preparedSelectedCode plans (Function.update x t true) piCode++
    [.single t .hadamard]


def preparedAdjacentRotationCode {n : ℕ} (plans : List (PreparedPauliPlan n))
    (t : Fin n) (x : Bits n) (a : AngleCode) : WordCode n :=
  [.single t (.inverse .yBasis)]++
    preparedSelectedCode plans (Function.update x t false) a++
    preparedSelectedCode plans (Function.update x t true) a.neg++[.single t .yBasis]


def preparedOrientedRotationCode {n : ℕ} (plans : List (PreparedPauliPlan n))
    (t : Fin n) (x : Bits n) (a : AngleCode) : WordCode n :=
  preparedAdjacentRotationCode plans t x (signedCode a (x t))


theorem preparedAdjacentSwapCode_eq {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) :
    preparedAdjacentSwapCode (preparedMaskTable hn) t x=adjacentSwapCode hn t x := by
  simp only [preparedAdjacentSwapCode,adjacentSwapCode,preparedSelectedCode_eq]


theorem preparedAdjacentRotationCode_eq {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) (a : AngleCode) :
    preparedAdjacentRotationCode (preparedMaskTable hn) t x a=adjacentRotationCode hn t x a := by
  simp only [preparedAdjacentRotationCode,adjacentRotationCode,preparedSelectedCode_eq]


theorem preparedOrientedRotationCode_eq {n : ℕ} (hn : 0<n) (t : Fin n) (x : Bits n) (a : AngleCode) :
    preparedOrientedRotationCode (preparedMaskTable hn) t x a=orientedRotationCode hn t x a := by
  simp only [preparedOrientedRotationCode,orientedRotationCode,preparedAdjacentRotationCode_eq]


def preparedMoveCode {n : ℕ} (plans : List (PreparedPauliPlan n)) (x : Bits n) :
    List (Fin n) → Bits n → WordCode n
  | [],_ => []
  | j::js,y => if y j=x j then preparedMoveCode plans x js y else
      preparedAdjacentSwapCode plans j y++preparedMoveCode plans x js (Function.update y j (x j))


theorem preparedMoveCode_eq {n : ℕ} (hn : 0<n) (x : Bits n) (js : List (Fin n)) (y : Bits n) :
    preparedMoveCode (preparedMaskTable hn) x js y=moveCode hn x js y := by
  induction js generalizing y with
  | nil => rfl
  | cons j js ih => simp only [preparedMoveCode,moveCode,preparedAdjacentSwapCode_eq,ih]


def preparedSwapCode {n : ℕ} (plans : List (PreparedPauliPlan n)) (x y : Bits n) : WordCode n :=
  if h : x=y then [] else
    let t:=differingWire x y h
    let a:=preparedMoveCode plans x (otherWires t) y
    a++preparedAdjacentSwapCode plans t x++reverseCode a


theorem preparedSwapCode_eq {n : ℕ} (hn : 0<n) (x y : Bits n) :
    preparedSwapCode (preparedMaskTable hn) x y=swapCode hn x y := by
  simp only [preparedSwapCode,swapCode,preparedMoveCode_eq,preparedAdjacentSwapCode_eq]


def preparedRotationCode {n : ℕ} (plans : List (PreparedPauliPlan n))
    (x y : Bits n) (h : x≠y) (a : AngleCode) : WordCode n :=
  let t:=differingWire x y h
  let b:=preparedMoveCode plans x (otherWires t) y
  b++preparedOrientedRotationCode plans t x a++reverseCode b


theorem preparedRotationCode_eq {n : ℕ} (hn : 0<n)
    (x y : Bits n) (h : x≠y) (a : AngleCode) :
    preparedRotationCode (preparedMaskTable hn) x y h a=rotationCode hn x y h a := by
  simp only [preparedRotationCode,rotationCode,preparedMoveCode_eq,preparedOrientedRotationCode_eq]


def preparedRawCompile {n : ℕ} (plans : List (PreparedPauliPlan n)) : RawCode n → WordCode n
  | .swap x y => preparedSwapCode plans x y
  | .merge x y h A B j => preparedRotationCode plans x y h (mergeCode A B j)


theorem preparedRawCompile_eq {n : ℕ} (hn : 0<n) (g : RawCode n) :
    preparedRawCompile (preparedMaskTable hn) g=g.compile hn := by
  cases g <;> simp only [preparedRawCompile,RawCode.compile,preparedSwapCode_eq,preparedRotationCode_eq]


def preparedCompileRaw {n : ℕ} (plans : List (PreparedPauliPlan n)) (xs : List (RawCode n)) : WordCode n :=
  xs.flatMap (preparedRawCompile plans)


theorem preparedCompileRaw_eq {n : ℕ} (hn : 0<n) (xs : List (RawCode n)) :
    preparedCompileRaw (preparedMaskTable hn) xs=compileRaw hn xs := by
  have he : preparedRawCompile (preparedMaskTable hn)=RawCode.compile hn :=
    funext (preparedRawCompile_eq hn)
  simp only [preparedCompileRaw,compileRaw,he]

end EffectiveEncoding
