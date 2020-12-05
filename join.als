enum S {A,B,C}
fun x : S->S->S { A->B->C }
fun y : S->S->S { C->B ->A}
assert join {
  x . y = A -> B ->B ->A
}
check join

/*
fun z: S->S->S { C->B->A + C->A->A } 

assert morejoin {
  x . z = {A -> B ->B ->A + 
              A -> B ->A ->A }
}

check morejoin
*/
