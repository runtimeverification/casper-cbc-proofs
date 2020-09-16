(*
Given a composite state, consider the following definitions:

- getObservations(s, v) : state -> validator -> set observation
  getObservations(s, v) = all observations contained in state s of validator v.

- equivFor(s, v) : state -> validator -> set validator
  equivFor(s, v) = all validators <w> for which <v> has evidence of equivocation.
  

- GH(s) : state -> set validator
  GH(s) = {w | not exists evidence of equivocation for w in union(getObservations(s[v], v) | v in V)} 
          (GH stands roughly for for "Globally Honest-Looking").
  
- GE(s) : state -> set validator
  GE(s) = V \ GH(s) (all the other ones, i.e "Globally-Provable Equivocating")
  
- HH(s) : state -> set validator
  HH(s) = {w | {w | not exists evidence of equivocation for w in union(getObservations(s[v], v) | v in GH(s))}}
          (HH stands roughly for "Honest-Looking for the Honest")
  
- HE(s) : state -> set validator
  HE(s) = V \ HH(s)

The statement of the common futures theorem:

Given any protocol composite state <s>, there exists a state <s'> such that
1. <s'> is a future state of <s>.
2. GH(s) = GH(s')
3. forall (i j : GH(s')) equivFor(s, i) = HH(s').
4. forall (i j : GH(s')) (e : HH(s')) project i e = project j e. 
*)