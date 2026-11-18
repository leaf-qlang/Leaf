module Backend.OpenQASM3.SerializerTest

import Expect

import Data.Fin
import Data.Vect
import Compiler.Backend.OpenQASM3.Serializer
import DSL.Control
import DSL.Core
import DSL.Gates

%default total

export
runSerializerTests : IO Bool
runSerializerTests = runTests $ Test.do
  test "an uncontrolled gate keeps its register name" $
    unitaryToOpenQasm3 "register" (H {n = 1} 0) `shouldBe` "h register[0];"

  test "a wrapper without controls emits the inner gate" $
    unitaryToOpenQasm3 "q" (Controlled {n = 1} [] [] (H 0)) `shouldBe` "h q[0];"

  test "a zero control uses negctrl" $
    unitaryToOpenQasm3 "q" (Controlled {n = 2} [0] [Zero] (X 1)) `shouldBe`
      "negctrl @ x q[0], q[1];"

  test "a one control uses ctrl" $
    unitaryToOpenQasm3 "q" (Controlled {n = 2} [0] [One] (X 1)) `shouldBe`
      "ctrl @ x q[0], q[1];"

  test "a plus control changes basis around a negative control" $
    unitaryToOpenQasm3 "q" (Controlled {n = 2} [0] [Plus] (X 1)) `shouldBe`
      "h q[0];\nnegctrl @ x q[0], q[1];\nh q[0];"

  test "a minus control changes basis around a positive control" $
    unitaryToOpenQasm3 "q" (Controlled {n = 2} [0] [Minus] (X 1)) `shouldBe`
      "h q[0];\nctrl @ x q[0], q[1];\nh q[0];"

  test "a plus-i control applies S-dagger then H and restores with H then S" $
    unitaryToOpenQasm3 "q" (Controlled {n = 2} [0] [PlusI] (X 1)) `shouldBe`
      "sdg q[0];\nh q[0];\nnegctrl @ x q[0], q[1];\nh q[0];\ns q[0];"

  test "a minus-i control uses the opposite computational polarity to plus-i" $
    unitaryToOpenQasm3 "q" (Controlled {n = 2} [0] [MinusI] (X 1)) `shouldBe`
      "sdg q[0];\nh q[0];\nctrl @ x q[0], q[1];\nh q[0];\ns q[0];"

  test "nested controls retain their states, wire order and gate parameters" $
    unitaryToOpenQasm3 "qs"
      (Controlled {n = 3} [0] [PlusI]
        (Controlled [1] [Minus] (RZ (MkRadians 0.25) 2))) `shouldBe`
      joinWith "\n"
        [ "sdg qs[0];"
        , "h qs[0];"
        , "h qs[1];"
        , "negctrl @ ctrl @ rz(0.25) qs[0], qs[1], qs[2];"
        , "h qs[1];"
        , "h qs[0];"
        , "s qs[0];"
        ]

  test "mixed controls change only control wires and restore them in reverse order" $
    coreGateToOpenQasm3 "q"
      (MkCoreGate {n = 7} [Zero, One, Plus, Minus, PlusI, MinusI] "x" [] [0, 1, 2, 3, 4, 5, 6]) `shouldBe`
      joinWith "\n"
        [ "h q[2];"
        , "h q[3];"
        , "sdg q[4];"
        , "h q[4];"
        , "sdg q[5];"
        , "h q[5];"
        , "negctrl @ ctrl @ negctrl @ ctrl @ negctrl @ ctrl @ x q[0], q[1], q[2], q[3], q[4], q[5], q[6];"
        , "h q[5];"
        , "s q[5];"
        , "h q[4];"
        , "s q[4];"
        , "h q[3];"
        , "h q[2];"
        ]
