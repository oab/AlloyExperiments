sig Node {
  adj: set Node,
} {not this in adj }

assert clique {
  all n1,n2:Node | n2 in n1.*adj
}

check clique for 5 Node

