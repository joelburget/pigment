-- Let's have some natural numbers...
data Nat := (zero : Nat) ; (suc : Nat -> Nat) ;

-- Now we can write plus like this:
let plus (m : Nat)(n : Nat) : Nat ;
<= Nat.Ind m ;
define plus 'zero n := n ;
define plus ('suc k) n := 'suc (plus k n) ;

-- Just to show this really works:
root ;
elab plus ('suc ('suc 'zero)) ('suc ('suc 'zero)) ;


-- Now we will prove that plus is commutative. First, some useful gadgetry...

-- Substitutivity of equality:
make ship : (X : Set)(x : X)(y : X)(q : :- x == y)(P : X -> Set) -> P x -> P y ;
lambda X, x, y, q, P, px ;
give coe (P x) (P y) ?q px ;
give con (refl (X -> Set) P % x y _) ;
root ;

-- Transitivity of equality:
make trans : :- ((X : Set)(a : X)(b : X)(c : X) => a == b => b == c => a == c) ;
lambda X, a, b, c, p, q ;
<= ship X a b _ ;
root ;

-- Reversing the order of arguments to functions:
make flip := (\ f k n -> f n k) : (Nat -> Nat -> Nat) -> Nat -> Nat -> Nat ;


-- And here come the proofs...

-- A lemma:
make plusZ : :- ((m : Nat) => plus m 'zero == m) ;
lambda m ;
<= Nat.Ind m ;
root ; 

-- Another lemma:
make plusS : :- ((k : Nat)(n : Nat) => plus k ('suc n) == (: Nat) ('suc (plus k n))) ;
lambda k, n ;
<= Nat.Ind k ;
give xf n ;
root ;

-- Given some arguments, plus is commutative:
make plusComm : :- ((k : Nat)(n : Nat) => plus k n == plus n k) ;
lambda k, n ;
<= Nat.Ind n ;
give plusZ k ;
give trans Nat (plus k ('suc xf^1)) ('suc (plus k xf^1)) ('suc (plus xf^1 k)) (plusS k xf^1) ? ;
simplify ;
give xf k ;
root ;

-- We really have equality between the *functions* |plus| and |flip plus|:
make plusCommF : :- (flip plus == plus) ;
simplify ;
lambda k1, k2, p, n1, n2, q ;
<= ship Nat k1 k2 _ ;
<= ship Nat n1 n2 _ ; 
give plusComm n1^1 k1 ;
root ;