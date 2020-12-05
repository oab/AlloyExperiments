enum value {A,B,C}

one sig Switch {
  state: value
} 
assert switch {
  all x:Switch | x.state = A or x.state = B or x.state = C
}

check switch

 
