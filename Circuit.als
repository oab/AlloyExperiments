let Bit = (0+1)

let andTable = { b0:Bit, b1:Bit, out:mul[b0,b1] }
let orTable    = { b0:Bit, b1:Bit, out:sum[b0+b1] }
let notTable = { b0:Bit, out:minus[1,b0] }
let xorTable = {
  b0:Bit, 
  b1:Bit, 
  out:andTable[orTable[b0,b1],notTable[andTable[b0,b1]]]
}

pred fullAdder(b0: Int, b1: Int, carryIn: Int, out: Int, carryOut: Int) {
  let xor = xorTable[b0, b1] {
    out = xorTable[xor, carryOut]
    carryOut = orTable[andTable[b0, b1], andTable[xor, carryIn]]
  }
}

pred rippleAdder[a0,a1,a2,a3,a4,a5,a6,a7,
                            b0,b1,b2,b3,b4,b5,b6,b7,
                            o0,o1,o2,o3,o4,o5,o6,o7, 
                            c0,c1,c2,c3,c4,c5,c6,c7 : Bit] {
   fullAdder[a0,b0,0,o0,c0] 
   fullAdder[a1,b1,c0,o1,c1] 
   fullAdder[a2,b2,c1,o2,c2]
   fullAdder[a3,b3,c2,o3,c3]
   fullAdder[a4,b4,c3,o4,c4]
   fullAdder[a5,b5,c4,o5,c5]
   fullAdder[a6,b6,c5,o6,c6]
   fullAdder[a7,b7,c6,o7,c7]
    
}

abstract sig Byte{
  values: (0 + 1 + 2 + 3 +4 +5+6+7) -> one Bit,
}
one sig B0, B1, O ,C extends Byte { }

pred rippleadd[b0: Byte, b1: Byte, o:Byte, c:Byte] {
  rippleAdder[b0.values[0], b0.values[1], b0.values[2], b0.values[3], b0.values[4], b0.values[5], b0.values[6], b0.values[7],
                      b1.values[0], b1.values[1], b1.values[2], b1.values[3], b1.values[4], b1.values[5], b1.values[6], b1.values[7],
                      o.values[0], o.values[1], o.values[2], o.values[3], o.values[4], o.values[5], o.values[6], o.values[7],
                      c.values[0], c.values[1], c.values[2], c.values[3], c.values[4], c.values[5], c.values[6], c.values[7]]
}

assert commutative {
 some x:Byte | rippleadd[B0,B1,O,C] => rippleadd[B1,B0,O,x] 
}

check commutative

