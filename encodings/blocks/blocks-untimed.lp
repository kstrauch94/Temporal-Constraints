time(0..horizon).

action(move(B,L)) :- block(B), loc(L), B != L.


on(B,B2,0) :- init(on(B,B2)).


{do(A,T) : action(A)} 1 :- time(T), T>0.
1 {on(B,L,T) : loc(L)} 1 :- block(B), time(T), T>0.

clear(B,T) :- not on(B2,B,T) : block(B2), B2 != B; block(B), time(T).
clear(table,T) :- time(T).

%precondition
:- do(move(B,L),T), not clear(L,T-1).
:- do(move(B,L),T), not clear(B,T-1).

%&constraint(1,horizon){+.do(move(B,L)) ; -~clear(L)} :- block(B), loc(L).
%&constraint(1,horizon){+.do(move(B,L)) ; -~clear(B)} :- block(B), loc(L).

%postcodition
:- do(move(B,L),T), not on(B,L,T).
%on(B,L,T) :- do(move(B,L),T).

%&constraint(1,horizon){+.do(move(B,L)) ; -.on(B,L)} :- block(B), loc(L).

%inertia
%on(B,L,T) :- on(B,L,T-1), not do(move(B,L2), T) : loc(L2), L2 != L ; time(T), T>0.
:- on(B,L,T), not on(B,L,T-1), not do(move(B,L),T), block(B), time(T), T>0.
%&constraint(1,horizon){+.on(B,L); -~on(B,L); -.do(move(B,L))} :- block(B), loc(L).


% cant have 2 blocks on 1 block
%:- on(B1,B,T), on(B2,B,T), B1 != B2, block(B).
&constraint(0,horizon,b2b){+.on(B1,B) ; +.on(B2,B)} :- block(B), block(B1), block(B2), B1 < B2.

% cant have 1 block on 2 blocks
%:- on(B,B1,T), on(B,B2,T), B1 != B2.
&constraint(0,horizon,bb2){+.on(B,B1) ; +.on(B,B2)} :- block(B), block(B1), block(B2), B1 < B2.

%:- on(B1,B2,T), on(B2,B1,T).
&constraint(0,horizon,bb){+.on(B1,B2) ; +.on(B2,B1)} :- block(B1), block(B2), B2 != B1.

:- on(B,B,T), time(T).

:- not on(B,L,horizon), goal(on(B,L)).

&signature{++do(move(B,L)) ; --do(move(B,L)) } :- block(B), loc(L).
&signature{--clear(L)} :- loc(L).
&signature{++on(B,L) ; --on(B,L)} :- block(B), loc(L).

#show do/2.
%#show on/3.