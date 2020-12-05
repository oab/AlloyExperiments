sig Item {} {Item in Stack.top}
abstract sig Stack {
  top    :   lone Item,
  substack : lone Stack
} 
one sig EStack extends Stack {} {no substack && no top}
sig NEStack extends Stack {} {one substack && one top}

fact irreflexive {no s:Stack | s = s.substack }
fact antisymmetric {
  no s1,s2 : Stack | s1 = s2.substack && s2 = s1.substack
}
pred hasEnd[s:Stack] {some e:EStack | e in s.^substack}
fact ends {all s:NEStack | hasEnd[s]}

pred reaches[s1:Stack,s2:Stack] {s2 in s1.^substack}

assert acyclic {
  no s1,s2 : Stack | s1.reaches[s2] && s2.reaches[s1]
}

//check acyclic for 5

