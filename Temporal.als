open util/ordering[GCD] as ord
sig GCD {
  x0: Int,
  x1: Int 
}
fun mk[a,b:Int]:GCD { {s:GCD| s.x0 = a && s.x1=b} }
fun gcd[x:GCD]:GCD  {
   { x':GCD | (x.x0 = x.x1)  => 
              x' =mk[x.x0, x.x1] else
    (x.x0 > x.x1)  => 
             x' =mk[sub[x.x0, x.x1],x.x1] else
             x' = mk[x.x0,sub[x.x1,x.x0]] } 
}
pred step[x,x':GCD] {
  x' = gcd[x]
}
fact Trace {  
  ord/first = mk[80,12]
  all g:GCD - ord/last | 
   let g' = g.next | step[g,g']
}

run {ord/last = mk[4,4]} for 8 Int, 9 GCD
/*
0 = 80 12
1 = 68 12
2 = 56 12
3 = 44 12
4 = 32 12
5 = 20 12
6 = 8 12
7 = 8 4
8 = 4 4
*/
