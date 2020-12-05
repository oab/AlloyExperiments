sig Item {} { Item in Stack.top} 
abstract sig Stack {
  top    :   lone Item,
  substack : lone Stack
}
one sig EStack extends Stack {} {no top && no substack}
sig NEStack extends Stack {} {one top && one substack}
fun empty[]:Stack { EStack }
fun push[s:Stack,i:Item]:Stack { 
  {r:Stack | r.substack = s && r.top = i}
}
fun pop[s:NEStack]:Stack { 
  {r:Stack | s.substack = r}
}
fact {
   Stack in empty[].*{x:Stack, y:x.push[Item]}
}
assert irreflexive {no s:Stack | s = s.substack }
check irreflexive
assert antisymmetric {
  no s1,s2 : Stack  | s1 = s2.substack && s2 = s1.substack
}
check antisymmetric


