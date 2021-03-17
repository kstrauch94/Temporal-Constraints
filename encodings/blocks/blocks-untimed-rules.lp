
time(0..horizon).

action(move(B,L)) :- block(B), loc(L), B != L.


on(B,B2,0) :- init(on(B,B2)).


1{do(A,T) : action(A)}1 :- time(T), T>0.

clear(B,T) :- not on(B2,B,T), block(B), block(B2), B2 != B, time(T).
clear(table,T) :- time(T).

%precondition
poss(move(B,L),T) :- clear(L,T-1), clear(B,T-1).
:- do(A,T), not poss(A,T).

%postcodition
on(B,L,T) :- do(move(B,L),T).

%inertia
on(B,L,T) :- on(B,L,T-1), not do(move(B,L2),T): loc(L2), L2!=L; block(B), time(T), T>0.


% cant have 2 blocks on 1 block
%:- on(B1,B,T), on(B2,B,T), B1 != B2, block(B).
&constraint(0,horizon){+.on(B1,B) ; +.on(B2,B)} :- block(B), block(B1), block(B2), B1 < B2.

% cant have 1 block on 2 blocks
%:- on(B,B1,T), on(B,B2,T), B1 != B2.
&constraint(0,horizon){+.on(B,B1) ; +.on(B,B2)} :- block(B), block(B1), block(B2), B1 < B2.

%:- on(B1,B2,T), on(B2,B1,T).
&constraint(0,horizon){+.on(B1,B2) ; +.on(B2,B1)} :- block(B1), block(B2), B2 != B1.

:- on(B,B,T), time(T).

:- not on(B,L,horizon), goal(on(B,L)).

&signature{++do(move(B,L)) ; --do(move(B,L)) } :- block(B), loc(L).
&signature{--clear(L)} :- loc(L).
&signature{++on(B,L) ; --on(B,L)} :- block(B), loc(L).
