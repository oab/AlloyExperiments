sig Item {} { Item in Stack.top} 
abstract sig Stack {
  top         : lone Item,
  substack : lone Stack
}
one sig EStack extends Stack {} {no top && no substack}
sig NEStack extends Stack {} {one top && one substack}
fun empty:Stack { EStack }
fun push[s:Stack,i:Item]:Stack { 
  {r:Stack | r.substack = s && r.top = i}
}
fun pop[s:NEStack]:Stack { 
  {r:Stack | s.substack = r}
}
fact { one x,y,z : Item |
   Stack in empty + 
                empty.push[x] + 
                empty.push[x].push[y] +
                empty.push[x].push[y].push[z] }
assert irreflexive {no s:Stack | s = s.substack }
//check irreflexive
assert antisymmetric {
  no s1,s2 : Stack  | s1 = s2.substack && s2 = s1.substack
}
//check antisymmetric



