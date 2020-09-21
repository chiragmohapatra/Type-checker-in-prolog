hastype(Gamma , unit , tunit).
hastype(Gamma , int(N) , tint).
hastype(Gamma , bool(true) , tbool).
hastype(Gamma , bool(false) , tbool).

hastype(Gamma , neg(E) , tint) :- hastype(Gamma , E , tint).
hastype(Gamma , add(E1,E2) , tint) :- hastype(Gamma , E1 , tint) , hastype(Gamma , E2 , tint) , !.
hastype(Gamma , diff(E1,E2) , tint) :- hastype(Gamma , E1 , tint) , hastype(Gamma , E2 , tint) , !.
hastype(Gamma , mult(E1,E2) , tint) :- hastype(Gamma , E1 , tint) , hastype(Gamma , E2 , tint) , !.
hastype(Gamma , div(E1,E2) , tint) :- hastype(Gamma , E1 , tint) , hastype(Gamma , E2 , tint) , !.
hastype(Gamma , mod(E1,E2) , tint) :- hastype(Gamma , E1 , tint) , hastype(Gamma , E2 , tint) , !.

hastype(Gamma , not(E) , tbool) :- hastype(Gamma , E , tbool).
hastype(Gamma , and(E1,E2) , tbool) :- hastype(Gamma , E1 , tbool) , hastype(Gamma , E2 , tbool) , !.
hastype(Gamma , or(E1,E2) , tbool) :- hastype(Gamma , E1 , tbool) , hastype(Gamma , E2 , tbool) , !.
hastype(Gamma , imp(E1,E2) , tbool) :- hastype(Gamma , E1 , tbool) , hastype(Gamma , E2 , tbool) , !.

hastype(Gamma , gt(E1,E2) , tbool) :- hastype(Gamma , E1 , tint) , hastype(Gamma , E2 , tint) , !.
hastype(Gamma , gteq(E1,E2) , tbool) :- hastype(Gamma , E1 , tint) , hastype(Gamma , E2 , tint) , !.
hastype(Gamma , lt(E1,E2) , tbool) :- hastype(Gamma , E1 , tint) , hastype(Gamma , E2 , tint) , !.
hastype(Gamma , lteq(E1,E2) , tbool) :- hastype(Gamma , E1 , tint) , hastype(Gamma , E2 , tint) , !.

hastype(Gamma , eq(E1,E2) , tbool) :- hastype(Gamma , E1 , T) , hastype(Gamma , E2 , T) , !.

hastype(Gamma , ifthenelse(E1,E2,E3) , T) :- hastype(Gamma , E1 , tbool) , hastype(Gamma , E2 , T) , hastype(Gamma , E3 , T) , !.

hastype(Gamma, abstraction(variable(X), E1), arrow(T1, T2)) :- hastype(Gamma, variable(X), T1), hastype([(variable(X), T1)|Gamma], E1, T2) , !.
hastype(Gamma , application(E1,E2) , T2) :- hastype(Gamma , E1 , arrow(T1,T2)) , hastype(Gamma , E2 , T1) , !.

/* this predicate checks if the first element X in a pair (X,Y) already occurs as a first element in the list */
member_first(X,[]) :- fail.
member_first((X,Y) , [(X,Z)|Xs]).
member_first(X , [Y|Ys]) :- member_first(X , Ys) , !.

/* the superceded union means that the second parameter superceded the first in case of conflicts */
superceded_union([],X,X).
superceded_union([X|Xs],Y,Z) :- superceded_union(Xs,[X|Y],Z) , \+ member_first(X,Y) , !.
superceded_union([X|Xs],Y,Z) :- superceded_union(Xs,Y,Z) , member_first(X,Y) , !.

lookup(Xs, variable(X), T) :- member((X, T), Xs) , !.

hastype(Gamma, variable(X), T) :- lookup(Gamma, variable(X), T).

typeElaborates(Gamma, x_is_e(variable(X), E), [(X, T)]) :- hastype(Gamma, E, T).
typeElaborates(Gamma, sequential(E1, E2), Gamma4) :- typeElaborates(Gamma, E1, Gamma1), superceded_union(Gamma, Gamma1, Gamma2), typeElaborates(Gamma2, E2, Gamma3), superceded_union(Gamma2, Gamma3, Gamma4) , !.
typeElaborates(Gamma, parallel(E1, E2), Gamma3) :- typeElaborates(Gamma, E1, Gamma1), typeElaborates(Gamma, E2, Gamma2), superceded_union(Gamma1, Gamma2, Gamma3) , !.
typeElaborates(Gamma, d1_in_d2(E1, E2), Gamma3) :- typeElaborates(Gamma, E1, Gamma1), superceded_union(Gamma, Gamma1, Gamma2) , typeElaborates(Gamma2, E2, Gamma3) , !.

hastype(Gamma, let_d_in_e(E1, E2), T) :- typeElaborates(Gamma, E1, Gamma1), superceded_union(Gamma, Gamma1, Gamma2), hastype(Gamma2, E2, T) , !.
hastype(Gamma, let_x_in_e(variable(X), E1, E2), T) :- hastype(Gamma, E1, T1), hastype([(X,T1)|Gamma], E2, T) , !.

hastype(Gamma, nTuple([]), tnTuple([])) :- !.
hastype(Gamma, nTuple([E1|Es]), tnTuple([T1|Ts])) :- hastype(Gamma, E1, T1), hastype(Gamma, nTuple(Es), tnTuple(Ts)).

hastype(Gamma, proj(0, nTuple([E1|Es])), T) :- hastype(Gamma, E1, T).
hastype(Gamma, proj(N, nTuple([E1|Es])), T) :- hastype(Gamma, proj(N1, nTuple(Es)), T), N is N1 + 1.




/* Test cases */

/* basic cases */
?- hastype([] , unit , T).
?- hastype([] , bool(false) , T).
?- hastype([] , int(5) , T).

/* expressions with only intants */
?- hastype([] , neg(int(5)) , T).
?- hastype([] , add(int(4) , int(3)) , T).
?- hastype([] , diff(int(12) , bool(true)) , T). /* false */
?- hastype([] , mult(int(5) , neg(int(3))) , T).
?- hastype([] , div(int(6) , mod(int(2) , int(4))) , T).

?- hastype([] , and(bool(true) , bool(false)) , T).
?- hastype([] , or(int(4) , bool(true)) , T). /* false */
?- hastype([], or(bool(true), and(bool(true), bool(false))), T).
?- hastype([], or(bool(true)), T). /* false */
?- hastype([], and(eq(int(2), int(4)), lt(int(2), int(3))), T).
?- hastype([], and(add(int(2), int(4)), gteq(int(2), int(3))), T). /* false */

/* expressions with variables */
?- lookup([(x , tint)] , variable(x) , T).
?- lookup([(z , tint)] , variable(x) , T). /* false */
?- lookup([(a , tunit) , (b , tbool) , (x , tint)] , variable(x) , T).

?- hastype([(x , tint)] , mult(int(4) , variable(x)) , T).
?- hastype([(x, tint), (z, tint)], and(eq(add(variable(x), int(1)), int(2)), variable(z)), T). /* false */
?- hastype([(x, tint), (z, tbool)], and(eq(add(variable(x), int(1)), int(2)), variable(z)), T). 
?- hastype([(x , tint) , (z , tbool)] , add(variable(x) , variable(x)) , T).

?- hastype([(z, tint), (x, tint)], ifthenelse(bool(true), int(2), variable(z)), T).
?- hastype([(z, tbool), (x, tint)], ifthenelse(bool(true), int(2), variable(z)), T). /* false */

?- hastype([(z, tbool), (x, tint)], nTuple([bool(true), unit, int(23), variable(z), variable(x)]), T).

?- hastype([(z, tbool), (x, tint)], proj(0, nTuple([bool(true), bool(false), int(23), variable(z), variable(x)])), T).
?- hastype([(z, tbool), (x, tint)], proj(4, nTuple([bool(true), bool(false), int(23), variable(z), variable(x)])), T).
?- hastype([(z, tbool), (x, tint)], proj(6, nTuple([bool(true), bool(false), int(23), variable(z), variable(x)])), T). /* false */
?- hastype([(z, tbool), (x, tint)], proj(N, nTuple([bool(true), bool(false), int(23), variable(z), variable(x)])), tint).   /* multiple possible values for N */

/* abstractions and applications */
?- hastype([(x, tint)], abstraction(variable(x), add(variable(x), int(45))), T).

?- hastype([(z, tbool), (x, tint)], application(abstraction(variable(z), and(variable(z), bool(false))), int(23)), T). /* false */
?- hastype([(z, tbool), (x, tint)], application(abstraction(variable(z), and(variable(z), bool(false))), bool(true)), T).

/* correctness of superceded_union */
?- superceded_union([(x,3),(y,4)],[(a,2),(x,5),(b,2)],Y).

/* checking local definitions */
?- typeElaborates([(z,tbool), (x, tint)], x_is_e(variable(z), bool(true)), W).
?- typeElaborates([(x, tint)], x_is_e(variable(z), bool(true)), W).
?- typeElaborates([(z,tbool), (x, tint)], parallel(x_is_e(variable(z), int(23)), x_is_e(variable(x), bool(true))), W).

/* highlighting the difference between parallel and sequential */
?- typeElaborates([(z,tbool), (x, tint)], sequential(x_is_e(variable(z), int(23)), x_is_e(variable(x), eq(int(6), variable(z)))), W).
?- typeElaborates([(z,tbool), (x, tint)], parallel(x_is_e(variable(z), int(23)), x_is_e(variable(x), eq(int(6), variable(z)))), W). /* false */

?- typeElaborates([(z,tbool), (x, tint)], d1_in_d2(x_is_e(variable(z), int(23)) , x_is_e(variable(x), lteq(variable(z),int(45)) ) ), W).
?- hastype([(z,tint), (x, tint)], let_x_in_e(variable(z), bool(true), and(variable(z), bool(false))), W).
?- hastype([], let_x_in_e(variable(z), bool(true), and(variable(z), bool(false))), W).
?- hastype([], let_d_in_e(parallel(x_is_e(variable(z), bool(true)), x_is_e(variable(x), bool(false))), and(variable(z),variable(x))), W).
?- hastype([], let_d_in_e(sequential(x_is_e(variable(z), bool(true)), x_is_e(variable(x), variable(z))), and(variable(z),variable(x))), W).
?- hastype([], let_d_in_e( d1_in_d2( x_is_e(variable(z), bool(true)), x_is_e(variable(x), and(variable(z),bool(false))) ),and(variable(x),variable(x))),W).

/* working as a type interference machine */
?- hastype([] , eq(X , int(4)) , tbool).
?- hastype([] , add(X , int(4)) , tint).    /* assign some garbage int value to X in all these cases */
?- hastype([] , add(X , int(4)) , T).

/* Ambiguous expressions */
?- hastype([], eq(add(A, B), subt(C, D)), T).   /* polymorphic type interference */
?- hastype([] , add(A,B) , T).  /* garbage values */
?- hastype(Gamma, eq(add(X,Y),add(A,B)), T).    /* gamma not specified : leads to garbage values */
?- hastype([] , eq(A,B) , T).   /* assigns random garbage values to A and B */

/* So , from the ambigous expressions , we see that our type checker cannot work as a polymorphic type interference engine */


/* official test cases */
?- hastype([(y,tbool),(x,tint)],lt(variable(x),int(23)),W).
?- hastype([(y,tbool),(x,tint)],nTuple([bool(true),bool(false),int(23),variable(y),variable(x)]),W).
?- typeElaborates([], sequential(x_is_e(variable(y), int(23)), x_is_e(variable(x), bool(true))), W).

